/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro, Johannes Hölzl

! This file was ported from Lean 3 source module algebra.order.group.defs
! leanprover-community/mathlib commit 448144f7ae193a8990cb7473c9e9a01990f64ac7
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Order.Hom.Basic
import Mathbin.Algebra.Order.Sub.Defs
import Mathbin.Algebra.Order.Monoid.Cancel.Defs

/-!
# Ordered groups

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
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
#align ordered_add_comm_group.to_covariant_class_left_le OrderedAddCommGroup.to_covariantClass_left_le

#print OrderedCommGroup.toOrderedCancelCommMonoid /-
-- See note [lower instance priority]
@[to_additive]
instance (priority := 100) OrderedCommGroup.toOrderedCancelCommMonoid [OrderedCommGroup α] :
    OrderedCancelCommMonoid α :=
  { ‹OrderedCommGroup α› with le_of_mul_le_mul_left := fun a b c => le_of_mul_le_mul_left' }
#align ordered_comm_group.to_ordered_cancel_comm_monoid OrderedCommGroup.toOrderedCancelCommMonoid
#align ordered_add_comm_group.to_ordered_cancel_add_comm_monoid OrderedAddCommGroup.toOrderedCancelAddCommMonoid
-/

example (α : Type u) [OrderedAddCommGroup α] : CovariantClass α α (swap (· + ·)) (· < ·) :=
  AddRightCancelSemigroup.covariant_swap_add_lt_of_covariant_swap_add_le α

/- warning: ordered_comm_group.to_contravariant_class_left_le -> OrderedCommGroup.to_contravariantClass_left_le is a dubious translation:
lean 3 declaration is
  forall (α : Type.{u1}) [_inst_1 : OrderedCommGroup.{u1} α], ContravariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α (OrderedCommGroup.toCommGroup.{u1} α _inst_1)))))))) (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1))))
but is expected to have type
  forall (α : Type.{u1}) [_inst_1 : OrderedCommGroup.{u1} α], ContravariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.244 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.246 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α (OrderedCommGroup.toCommGroup.{u1} α _inst_1))))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.244 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.246) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.259 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.261 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.259 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.261)
Case conversion may be inaccurate. Consider using '#align ordered_comm_group.to_contravariant_class_left_le OrderedCommGroup.to_contravariantClass_left_leₓ'. -/
/-- A choice-free shortcut instance. -/
@[to_additive "A choice-free shortcut instance."]
instance OrderedCommGroup.to_contravariantClass_left_le (α : Type u) [OrderedCommGroup α] :
    ContravariantClass α α (· * ·) (· ≤ ·)
    where elim a b c bc := by simpa using mul_le_mul_left' bc a⁻¹
#align ordered_comm_group.to_contravariant_class_left_le OrderedCommGroup.to_contravariantClass_left_le
#align ordered_add_comm_group.to_contravariant_class_left_le OrderedAddCommGroup.to_contravariantClass_left_le

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
#align ordered_comm_group.to_contravariant_class_right_le OrderedCommGroup.to_contravariantClass_right_le
#align ordered_add_comm_group.to_contravariant_class_right_le OrderedAddCommGroup.to_contravariantClass_right_le

section Group

variable [Group α]

section TypeclassesLeftLe

variable [LE α] [CovariantClass α α (· * ·) (· ≤ ·)] {a b c d : α}

/- warning: left.inv_le_one_iff -> Left.inv_le_one_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LE.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)))))) (LE.le.{u1} α _inst_2)] {a : α}, Iff (LE.le.{u1} α _inst_2 (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) a) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)))))))) (LE.le.{u1} α _inst_2 (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))))) a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LE.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.446 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.448 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.446 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.448) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.461 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.463 : α) => LE.le.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.461 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.463)] {a : α}, Iff (LE.le.{u1} α _inst_2 (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1)))) a) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (InvOneClass.toOne.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1))))))) (LE.le.{u1} α _inst_2 (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (InvOneClass.toOne.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1)))))) a)
Case conversion may be inaccurate. Consider using '#align left.inv_le_one_iff Left.inv_le_one_iffₓ'. -/
/-- Uses `left` co(ntra)variant. -/
@[simp, to_additive Left.neg_nonpos_iff "Uses `left` co(ntra)variant."]
theorem Left.inv_le_one_iff : a⁻¹ ≤ 1 ↔ 1 ≤ a :=
  by
  rw [← mul_le_mul_iff_left a]
  simp
#align left.inv_le_one_iff Left.inv_le_one_iff
#align left.neg_nonpos_iff Left.neg_nonpos_iff

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
#align left.nonneg_neg_iff Left.nonneg_neg_iff

/- warning: le_inv_mul_iff_mul_le -> le_inv_mul_iff_mul_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LE.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)))))) (LE.le.{u1} α _inst_2)] {a : α} {b : α} {c : α}, Iff (LE.le.{u1} α _inst_2 b (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) a) c)) (LE.le.{u1} α _inst_2 (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) a b) c)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LE.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.645 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.647 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.645 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.647) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.660 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.662 : α) => LE.le.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.660 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.662)] {a : α} {b : α} {c : α}, Iff (LE.le.{u1} α _inst_2 b (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1)))) a) c)) (LE.le.{u1} α _inst_2 (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) a b) c)
Case conversion may be inaccurate. Consider using '#align le_inv_mul_iff_mul_le le_inv_mul_iff_mul_leₓ'. -/
@[simp, to_additive]
theorem le_inv_mul_iff_mul_le : b ≤ a⁻¹ * c ↔ a * b ≤ c :=
  by
  rw [← mul_le_mul_iff_left a]
  simp
#align le_inv_mul_iff_mul_le le_inv_mul_iff_mul_le
#align le_neg_add_iff_add_le le_neg_add_iff_add_le

/- warning: inv_mul_le_iff_le_mul -> inv_mul_le_iff_le_mul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LE.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)))))) (LE.le.{u1} α _inst_2)] {a : α} {b : α} {c : α}, Iff (LE.le.{u1} α _inst_2 (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) b) a) c) (LE.le.{u1} α _inst_2 a (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) b c))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LE.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.746 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.748 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.746 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.748) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.761 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.763 : α) => LE.le.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.761 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.763)] {a : α} {b : α} {c : α}, Iff (LE.le.{u1} α _inst_2 (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1)))) b) a) c) (LE.le.{u1} α _inst_2 a (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) b c))
Case conversion may be inaccurate. Consider using '#align inv_mul_le_iff_le_mul inv_mul_le_iff_le_mulₓ'. -/
@[simp, to_additive]
theorem inv_mul_le_iff_le_mul : b⁻¹ * a ≤ c ↔ a ≤ b * c := by
  rw [← mul_le_mul_iff_left b, mul_inv_cancel_left]
#align inv_mul_le_iff_le_mul inv_mul_le_iff_le_mul
#align neg_add_le_iff_le_add neg_add_le_iff_le_add

/- warning: inv_le_iff_one_le_mul' -> inv_le_iff_one_le_mul' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LE.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)))))) (LE.le.{u1} α _inst_2)] {a : α} {b : α}, Iff (LE.le.{u1} α _inst_2 (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) a) b) (LE.le.{u1} α _inst_2 (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) a b))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LE.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.843 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.845 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.843 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.845) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.858 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.860 : α) => LE.le.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.858 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.860)] {a : α} {b : α}, Iff (LE.le.{u1} α _inst_2 (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1)))) a) b) (LE.le.{u1} α _inst_2 (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (InvOneClass.toOne.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1)))))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) a b))
Case conversion may be inaccurate. Consider using '#align inv_le_iff_one_le_mul' inv_le_iff_one_le_mul'ₓ'. -/
@[to_additive neg_le_iff_add_nonneg']
theorem inv_le_iff_one_le_mul' : a⁻¹ ≤ b ↔ 1 ≤ a * b :=
  (mul_le_mul_iff_left a).symm.trans <| by rw [mul_inv_self]
#align inv_le_iff_one_le_mul' inv_le_iff_one_le_mul'
#align neg_le_iff_add_nonneg' neg_le_iff_add_nonneg'

/- warning: le_inv_iff_mul_le_one_left -> le_inv_iff_mul_le_one_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LE.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)))))) (LE.le.{u1} α _inst_2)] {a : α} {b : α}, Iff (LE.le.{u1} α _inst_2 a (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) b)) (LE.le.{u1} α _inst_2 (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) b a) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LE.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.943 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.945 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.943 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.945) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.958 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.960 : α) => LE.le.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.958 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.960)] {a : α} {b : α}, Iff (LE.le.{u1} α _inst_2 a (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1)))) b)) (LE.le.{u1} α _inst_2 (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) b a) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (InvOneClass.toOne.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1)))))))
Case conversion may be inaccurate. Consider using '#align le_inv_iff_mul_le_one_left le_inv_iff_mul_le_one_leftₓ'. -/
@[to_additive]
theorem le_inv_iff_mul_le_one_left : a ≤ b⁻¹ ↔ b * a ≤ 1 :=
  (mul_le_mul_iff_left b).symm.trans <| by rw [mul_inv_self]
#align le_inv_iff_mul_le_one_left le_inv_iff_mul_le_one_left
#align le_neg_iff_add_nonpos_left le_neg_iff_add_nonpos_left

/- warning: le_inv_mul_iff_le -> le_inv_mul_iff_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LE.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)))))) (LE.le.{u1} α _inst_2)] {a : α} {b : α}, Iff (LE.le.{u1} α _inst_2 (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) b) a)) (LE.le.{u1} α _inst_2 b a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LE.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.1043 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.1045 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.1043 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.1045) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.1058 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.1060 : α) => LE.le.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.1058 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.1060)] {a : α} {b : α}, Iff (LE.le.{u1} α _inst_2 (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (InvOneClass.toOne.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1)))))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1)))) b) a)) (LE.le.{u1} α _inst_2 b a)
Case conversion may be inaccurate. Consider using '#align le_inv_mul_iff_le le_inv_mul_iff_leₓ'. -/
@[to_additive]
theorem le_inv_mul_iff_le : 1 ≤ b⁻¹ * a ↔ b ≤ a := by
  rw [← mul_le_mul_iff_left b, mul_one, mul_inv_cancel_left]
#align le_inv_mul_iff_le le_inv_mul_iff_le
#align le_neg_add_iff_le le_neg_add_iff_le

/- warning: inv_mul_le_one_iff -> inv_mul_le_one_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LE.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)))))) (LE.le.{u1} α _inst_2)] {a : α} {b : α}, Iff (LE.le.{u1} α _inst_2 (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) a) b) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)))))))) (LE.le.{u1} α _inst_2 b a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LE.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.1139 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.1141 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.1139 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.1141) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.1154 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.1156 : α) => LE.le.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.1154 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.1156)] {a : α} {b : α}, Iff (LE.le.{u1} α _inst_2 (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1)))) a) b) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (InvOneClass.toOne.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1))))))) (LE.le.{u1} α _inst_2 b a)
Case conversion may be inaccurate. Consider using '#align inv_mul_le_one_iff inv_mul_le_one_iffₓ'. -/
@[to_additive]
theorem inv_mul_le_one_iff : a⁻¹ * b ≤ 1 ↔ b ≤ a :=
  trans inv_mul_le_iff_le_mul <| by rw [mul_one]
#align inv_mul_le_one_iff inv_mul_le_one_iff
#align neg_add_nonpos_iff neg_add_nonpos_iff

end TypeclassesLeftLe

section TypeclassesLeftLt

variable [LT α] [CovariantClass α α (· * ·) (· < ·)] {a b c : α}

/- warning: left.one_lt_inv_iff -> Left.one_lt_inv_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LT.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)))))) (LT.lt.{u1} α _inst_2)] {a : α}, Iff (LT.lt.{u1} α _inst_2 (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))))) (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) a)) (LT.lt.{u1} α _inst_2 a (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LT.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.1291 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.1293 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.1291 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.1293) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.1306 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.1308 : α) => LT.lt.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.1306 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.1308)] {a : α}, Iff (LT.lt.{u1} α _inst_2 (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (InvOneClass.toOne.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1)))))) (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1)))) a)) (LT.lt.{u1} α _inst_2 a (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (InvOneClass.toOne.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1)))))))
Case conversion may be inaccurate. Consider using '#align left.one_lt_inv_iff Left.one_lt_inv_iffₓ'. -/
/-- Uses `left` co(ntra)variant. -/
@[simp, to_additive Left.neg_pos_iff "Uses `left` co(ntra)variant."]
theorem Left.one_lt_inv_iff : 1 < a⁻¹ ↔ a < 1 := by
  rw [← mul_lt_mul_iff_left a, mul_inv_self, mul_one]
#align left.one_lt_inv_iff Left.one_lt_inv_iff
#align left.neg_pos_iff Left.neg_pos_iff

/- warning: left.inv_lt_one_iff -> Left.inv_lt_one_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LT.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)))))) (LT.lt.{u1} α _inst_2)] {a : α}, Iff (LT.lt.{u1} α _inst_2 (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) a) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)))))))) (LT.lt.{u1} α _inst_2 (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))))) a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LT.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.1388 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.1390 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.1388 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.1390) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.1403 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.1405 : α) => LT.lt.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.1403 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.1405)] {a : α}, Iff (LT.lt.{u1} α _inst_2 (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1)))) a) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (InvOneClass.toOne.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1))))))) (LT.lt.{u1} α _inst_2 (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (InvOneClass.toOne.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1)))))) a)
Case conversion may be inaccurate. Consider using '#align left.inv_lt_one_iff Left.inv_lt_one_iffₓ'. -/
/-- Uses `left` co(ntra)variant. -/
@[simp, to_additive Left.neg_neg_iff "Uses `left` co(ntra)variant."]
theorem Left.inv_lt_one_iff : a⁻¹ < 1 ↔ 1 < a := by
  rw [← mul_lt_mul_iff_left a, mul_inv_self, mul_one]
#align left.inv_lt_one_iff Left.inv_lt_one_iff
#align left.neg_neg_iff Left.neg_neg_iff

/- warning: lt_inv_mul_iff_mul_lt -> lt_inv_mul_iff_mul_lt is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LT.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)))))) (LT.lt.{u1} α _inst_2)] {a : α} {b : α} {c : α}, Iff (LT.lt.{u1} α _inst_2 b (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) a) c)) (LT.lt.{u1} α _inst_2 (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) a b) c)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LT.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.1482 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.1484 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.1482 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.1484) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.1497 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.1499 : α) => LT.lt.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.1497 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.1499)] {a : α} {b : α} {c : α}, Iff (LT.lt.{u1} α _inst_2 b (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1)))) a) c)) (LT.lt.{u1} α _inst_2 (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) a b) c)
Case conversion may be inaccurate. Consider using '#align lt_inv_mul_iff_mul_lt lt_inv_mul_iff_mul_ltₓ'. -/
@[simp, to_additive]
theorem lt_inv_mul_iff_mul_lt : b < a⁻¹ * c ↔ a * b < c :=
  by
  rw [← mul_lt_mul_iff_left a]
  simp
#align lt_inv_mul_iff_mul_lt lt_inv_mul_iff_mul_lt
#align lt_neg_add_iff_add_lt lt_neg_add_iff_add_lt

/- warning: inv_mul_lt_iff_lt_mul -> inv_mul_lt_iff_lt_mul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LT.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)))))) (LT.lt.{u1} α _inst_2)] {a : α} {b : α} {c : α}, Iff (LT.lt.{u1} α _inst_2 (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) b) a) c) (LT.lt.{u1} α _inst_2 a (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) b c))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LT.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.1582 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.1584 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.1582 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.1584) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.1597 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.1599 : α) => LT.lt.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.1597 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.1599)] {a : α} {b : α} {c : α}, Iff (LT.lt.{u1} α _inst_2 (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1)))) b) a) c) (LT.lt.{u1} α _inst_2 a (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) b c))
Case conversion may be inaccurate. Consider using '#align inv_mul_lt_iff_lt_mul inv_mul_lt_iff_lt_mulₓ'. -/
@[simp, to_additive]
theorem inv_mul_lt_iff_lt_mul : b⁻¹ * a < c ↔ a < b * c := by
  rw [← mul_lt_mul_iff_left b, mul_inv_cancel_left]
#align inv_mul_lt_iff_lt_mul inv_mul_lt_iff_lt_mul
#align neg_add_lt_iff_lt_add neg_add_lt_iff_lt_add

/- warning: inv_lt_iff_one_lt_mul' -> inv_lt_iff_one_lt_mul' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LT.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)))))) (LT.lt.{u1} α _inst_2)] {a : α} {b : α}, Iff (LT.lt.{u1} α _inst_2 (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) a) b) (LT.lt.{u1} α _inst_2 (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) a b))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LT.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.1678 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.1680 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.1678 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.1680) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.1693 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.1695 : α) => LT.lt.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.1693 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.1695)] {a : α} {b : α}, Iff (LT.lt.{u1} α _inst_2 (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1)))) a) b) (LT.lt.{u1} α _inst_2 (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (InvOneClass.toOne.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1)))))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) a b))
Case conversion may be inaccurate. Consider using '#align inv_lt_iff_one_lt_mul' inv_lt_iff_one_lt_mul'ₓ'. -/
@[to_additive]
theorem inv_lt_iff_one_lt_mul' : a⁻¹ < b ↔ 1 < a * b :=
  (mul_lt_mul_iff_left a).symm.trans <| by rw [mul_inv_self]
#align inv_lt_iff_one_lt_mul' inv_lt_iff_one_lt_mul'
#align neg_lt_iff_pos_add' neg_lt_iff_pos_add'

/- warning: lt_inv_iff_mul_lt_one' -> lt_inv_iff_mul_lt_one' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LT.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)))))) (LT.lt.{u1} α _inst_2)] {a : α} {b : α}, Iff (LT.lt.{u1} α _inst_2 a (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) b)) (LT.lt.{u1} α _inst_2 (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) b a) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LT.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.1777 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.1779 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.1777 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.1779) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.1792 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.1794 : α) => LT.lt.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.1792 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.1794)] {a : α} {b : α}, Iff (LT.lt.{u1} α _inst_2 a (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1)))) b)) (LT.lt.{u1} α _inst_2 (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) b a) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (InvOneClass.toOne.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1)))))))
Case conversion may be inaccurate. Consider using '#align lt_inv_iff_mul_lt_one' lt_inv_iff_mul_lt_one'ₓ'. -/
@[to_additive]
theorem lt_inv_iff_mul_lt_one' : a < b⁻¹ ↔ b * a < 1 :=
  (mul_lt_mul_iff_left b).symm.trans <| by rw [mul_inv_self]
#align lt_inv_iff_mul_lt_one' lt_inv_iff_mul_lt_one'
#align lt_neg_iff_add_neg' lt_neg_iff_add_neg'

/- warning: lt_inv_mul_iff_lt -> lt_inv_mul_iff_lt is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LT.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)))))) (LT.lt.{u1} α _inst_2)] {a : α} {b : α}, Iff (LT.lt.{u1} α _inst_2 (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) b) a)) (LT.lt.{u1} α _inst_2 b a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LT.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.1876 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.1878 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.1876 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.1878) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.1891 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.1893 : α) => LT.lt.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.1891 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.1893)] {a : α} {b : α}, Iff (LT.lt.{u1} α _inst_2 (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (InvOneClass.toOne.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1)))))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1)))) b) a)) (LT.lt.{u1} α _inst_2 b a)
Case conversion may be inaccurate. Consider using '#align lt_inv_mul_iff_lt lt_inv_mul_iff_ltₓ'. -/
@[to_additive]
theorem lt_inv_mul_iff_lt : 1 < b⁻¹ * a ↔ b < a := by
  rw [← mul_lt_mul_iff_left b, mul_one, mul_inv_cancel_left]
#align lt_inv_mul_iff_lt lt_inv_mul_iff_lt
#align lt_neg_add_iff_lt lt_neg_add_iff_lt

/- warning: inv_mul_lt_one_iff -> inv_mul_lt_one_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LT.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)))))) (LT.lt.{u1} α _inst_2)] {a : α} {b : α}, Iff (LT.lt.{u1} α _inst_2 (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) a) b) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)))))))) (LT.lt.{u1} α _inst_2 b a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LT.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.1971 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.1973 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.1971 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.1973) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.1986 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.1988 : α) => LT.lt.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.1986 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.1988)] {a : α} {b : α}, Iff (LT.lt.{u1} α _inst_2 (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1)))) a) b) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (InvOneClass.toOne.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1))))))) (LT.lt.{u1} α _inst_2 b a)
Case conversion may be inaccurate. Consider using '#align inv_mul_lt_one_iff inv_mul_lt_one_iffₓ'. -/
@[to_additive]
theorem inv_mul_lt_one_iff : a⁻¹ * b < 1 ↔ b < a :=
  trans inv_mul_lt_iff_lt_mul <| by rw [mul_one]
#align inv_mul_lt_one_iff inv_mul_lt_one_iff
#align neg_add_neg_iff neg_add_neg_iff

end TypeclassesLeftLt

section TypeclassesRightLe

variable [LE α] [CovariantClass α α (swap (· * ·)) (· ≤ ·)] {a b c : α}

/- warning: right.inv_le_one_iff -> Right.inv_le_one_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LE.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))))) (LE.le.{u1} α _inst_2)] {a : α}, Iff (LE.le.{u1} α _inst_2 (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) a) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)))))))) (LE.le.{u1} α _inst_2 (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))))) a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LE.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.2128 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.2130 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.2128 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.2130)) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.2143 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.2145 : α) => LE.le.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.2143 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.2145)] {a : α}, Iff (LE.le.{u1} α _inst_2 (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1)))) a) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (InvOneClass.toOne.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1))))))) (LE.le.{u1} α _inst_2 (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (InvOneClass.toOne.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1)))))) a)
Case conversion may be inaccurate. Consider using '#align right.inv_le_one_iff Right.inv_le_one_iffₓ'. -/
/-- Uses `right` co(ntra)variant. -/
@[simp, to_additive Right.neg_nonpos_iff "Uses `right` co(ntra)variant."]
theorem Right.inv_le_one_iff : a⁻¹ ≤ 1 ↔ 1 ≤ a :=
  by
  rw [← mul_le_mul_iff_right a]
  simp
#align right.inv_le_one_iff Right.inv_le_one_iff
#align right.neg_nonpos_iff Right.neg_nonpos_iff

/- warning: right.one_le_inv_iff -> Right.one_le_inv_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LE.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))))) (LE.le.{u1} α _inst_2)] {a : α}, Iff (LE.le.{u1} α _inst_2 (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))))) (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) a)) (LE.le.{u1} α _inst_2 a (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LE.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.2231 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.2233 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.2231 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.2233)) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.2246 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.2248 : α) => LE.le.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.2246 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.2248)] {a : α}, Iff (LE.le.{u1} α _inst_2 (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (InvOneClass.toOne.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1)))))) (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1)))) a)) (LE.le.{u1} α _inst_2 a (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (InvOneClass.toOne.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1)))))))
Case conversion may be inaccurate. Consider using '#align right.one_le_inv_iff Right.one_le_inv_iffₓ'. -/
/-- Uses `right` co(ntra)variant. -/
@[simp, to_additive Right.nonneg_neg_iff "Uses `right` co(ntra)variant."]
theorem Right.one_le_inv_iff : 1 ≤ a⁻¹ ↔ a ≤ 1 :=
  by
  rw [← mul_le_mul_iff_right a]
  simp
#align right.one_le_inv_iff Right.one_le_inv_iff
#align right.nonneg_neg_iff Right.nonneg_neg_iff

/- warning: inv_le_iff_one_le_mul -> inv_le_iff_one_le_mul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LE.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))))) (LE.le.{u1} α _inst_2)] {a : α} {b : α}, Iff (LE.le.{u1} α _inst_2 (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) a) b) (LE.le.{u1} α _inst_2 (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) b a))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LE.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.2331 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.2333 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.2331 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.2333)) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.2346 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.2348 : α) => LE.le.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.2346 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.2348)] {a : α} {b : α}, Iff (LE.le.{u1} α _inst_2 (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1)))) a) b) (LE.le.{u1} α _inst_2 (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (InvOneClass.toOne.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1)))))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) b a))
Case conversion may be inaccurate. Consider using '#align inv_le_iff_one_le_mul inv_le_iff_one_le_mulₓ'. -/
@[to_additive neg_le_iff_add_nonneg]
theorem inv_le_iff_one_le_mul : a⁻¹ ≤ b ↔ 1 ≤ b * a :=
  (mul_le_mul_iff_right a).symm.trans <| by rw [inv_mul_self]
#align inv_le_iff_one_le_mul inv_le_iff_one_le_mul
#align neg_le_iff_add_nonneg neg_le_iff_add_nonneg

/- warning: le_inv_iff_mul_le_one_right -> le_inv_iff_mul_le_one_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LE.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))))) (LE.le.{u1} α _inst_2)] {a : α} {b : α}, Iff (LE.le.{u1} α _inst_2 a (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) b)) (LE.le.{u1} α _inst_2 (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) a b) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LE.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.2433 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.2435 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.2433 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.2435)) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.2448 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.2450 : α) => LE.le.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.2448 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.2450)] {a : α} {b : α}, Iff (LE.le.{u1} α _inst_2 a (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1)))) b)) (LE.le.{u1} α _inst_2 (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) a b) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (InvOneClass.toOne.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1)))))))
Case conversion may be inaccurate. Consider using '#align le_inv_iff_mul_le_one_right le_inv_iff_mul_le_one_rightₓ'. -/
@[to_additive]
theorem le_inv_iff_mul_le_one_right : a ≤ b⁻¹ ↔ a * b ≤ 1 :=
  (mul_le_mul_iff_right b).symm.trans <| by rw [inv_mul_self]
#align le_inv_iff_mul_le_one_right le_inv_iff_mul_le_one_right
#align le_neg_iff_add_nonpos_right le_neg_iff_add_nonpos_right

/- warning: mul_inv_le_iff_le_mul -> mul_inv_le_iff_le_mul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LE.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))))) (LE.le.{u1} α _inst_2)] {a : α} {b : α} {c : α}, Iff (LE.le.{u1} α _inst_2 (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) a (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) b)) c) (LE.le.{u1} α _inst_2 a (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) c b))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LE.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.2535 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.2537 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.2535 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.2537)) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.2550 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.2552 : α) => LE.le.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.2550 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.2552)] {a : α} {b : α} {c : α}, Iff (LE.le.{u1} α _inst_2 (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) a (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1)))) b)) c) (LE.le.{u1} α _inst_2 a (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) c b))
Case conversion may be inaccurate. Consider using '#align mul_inv_le_iff_le_mul mul_inv_le_iff_le_mulₓ'. -/
@[simp, to_additive]
theorem mul_inv_le_iff_le_mul : a * b⁻¹ ≤ c ↔ a ≤ c * b :=
  (mul_le_mul_iff_right b).symm.trans <| by rw [inv_mul_cancel_right]
#align mul_inv_le_iff_le_mul mul_inv_le_iff_le_mul
#align add_neg_le_iff_le_add add_neg_le_iff_le_add

/- warning: le_mul_inv_iff_mul_le -> le_mul_inv_iff_mul_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LE.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))))) (LE.le.{u1} α _inst_2)] {a : α} {b : α} {c : α}, Iff (LE.le.{u1} α _inst_2 c (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) a (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) b))) (LE.le.{u1} α _inst_2 (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) c b) a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LE.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.2639 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.2641 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.2639 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.2641)) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.2654 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.2656 : α) => LE.le.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.2654 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.2656)] {a : α} {b : α} {c : α}, Iff (LE.le.{u1} α _inst_2 c (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) a (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1)))) b))) (LE.le.{u1} α _inst_2 (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) c b) a)
Case conversion may be inaccurate. Consider using '#align le_mul_inv_iff_mul_le le_mul_inv_iff_mul_leₓ'. -/
@[simp, to_additive]
theorem le_mul_inv_iff_mul_le : c ≤ a * b⁻¹ ↔ c * b ≤ a :=
  (mul_le_mul_iff_right b).symm.trans <| by rw [inv_mul_cancel_right]
#align le_mul_inv_iff_mul_le le_mul_inv_iff_mul_le
#align le_add_neg_iff_add_le le_add_neg_iff_add_le

/- warning: mul_inv_le_one_iff_le -> mul_inv_le_one_iff_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LE.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))))) (LE.le.{u1} α _inst_2)] {a : α} {b : α}, Iff (LE.le.{u1} α _inst_2 (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) a (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) b)) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)))))))) (LE.le.{u1} α _inst_2 a b)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LE.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.2743 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.2745 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.2743 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.2745)) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.2758 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.2760 : α) => LE.le.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.2758 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.2760)] {a : α} {b : α}, Iff (LE.le.{u1} α _inst_2 (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) a (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1)))) b)) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (InvOneClass.toOne.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1))))))) (LE.le.{u1} α _inst_2 a b)
Case conversion may be inaccurate. Consider using '#align mul_inv_le_one_iff_le mul_inv_le_one_iff_leₓ'. -/
@[simp, to_additive]
theorem mul_inv_le_one_iff_le : a * b⁻¹ ≤ 1 ↔ a ≤ b :=
  mul_inv_le_iff_le_mul.trans <| by rw [one_mul]
#align mul_inv_le_one_iff_le mul_inv_le_one_iff_le
#align add_neg_nonpos_iff_le add_neg_nonpos_iff_le

/- warning: le_mul_inv_iff_le -> le_mul_inv_iff_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LE.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))))) (LE.le.{u1} α _inst_2)] {a : α} {b : α}, Iff (LE.le.{u1} α _inst_2 (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) a (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) b))) (LE.le.{u1} α _inst_2 b a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LE.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.2841 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.2843 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.2841 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.2843)) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.2856 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.2858 : α) => LE.le.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.2856 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.2858)] {a : α} {b : α}, Iff (LE.le.{u1} α _inst_2 (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (InvOneClass.toOne.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1)))))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) a (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1)))) b))) (LE.le.{u1} α _inst_2 b a)
Case conversion may be inaccurate. Consider using '#align le_mul_inv_iff_le le_mul_inv_iff_leₓ'. -/
@[to_additive]
theorem le_mul_inv_iff_le : 1 ≤ a * b⁻¹ ↔ b ≤ a := by
  rw [← mul_le_mul_iff_right b, one_mul, inv_mul_cancel_right]
#align le_mul_inv_iff_le le_mul_inv_iff_le
#align le_add_neg_iff_le le_add_neg_iff_le

/- warning: mul_inv_le_one_iff -> mul_inv_le_one_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LE.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))))) (LE.le.{u1} α _inst_2)] {a : α} {b : α}, Iff (LE.le.{u1} α _inst_2 (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) b (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) a)) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)))))))) (LE.le.{u1} α _inst_2 b a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LE.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.2939 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.2941 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.2939 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.2941)) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.2954 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.2956 : α) => LE.le.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.2954 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.2956)] {a : α} {b : α}, Iff (LE.le.{u1} α _inst_2 (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) b (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1)))) a)) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (InvOneClass.toOne.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1))))))) (LE.le.{u1} α _inst_2 b a)
Case conversion may be inaccurate. Consider using '#align mul_inv_le_one_iff mul_inv_le_one_iffₓ'. -/
@[to_additive]
theorem mul_inv_le_one_iff : b * a⁻¹ ≤ 1 ↔ b ≤ a :=
  trans mul_inv_le_iff_le_mul <| by rw [one_mul]
#align mul_inv_le_one_iff mul_inv_le_one_iff
#align add_neg_nonpos_iff add_neg_nonpos_iff

end TypeclassesRightLe

section TypeclassesRightLt

variable [LT α] [CovariantClass α α (swap (· * ·)) (· < ·)] {a b c : α}

/- warning: right.inv_lt_one_iff -> Right.inv_lt_one_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LT.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))))) (LT.lt.{u1} α _inst_2)] {a : α}, Iff (LT.lt.{u1} α _inst_2 (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) a) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)))))))) (LT.lt.{u1} α _inst_2 (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))))) a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LT.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.3096 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.3098 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.3096 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.3098)) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.3111 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.3113 : α) => LT.lt.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.3111 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.3113)] {a : α}, Iff (LT.lt.{u1} α _inst_2 (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1)))) a) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (InvOneClass.toOne.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1))))))) (LT.lt.{u1} α _inst_2 (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (InvOneClass.toOne.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1)))))) a)
Case conversion may be inaccurate. Consider using '#align right.inv_lt_one_iff Right.inv_lt_one_iffₓ'. -/
/-- Uses `right` co(ntra)variant. -/
@[simp, to_additive Right.neg_neg_iff "Uses `right` co(ntra)variant."]
theorem Right.inv_lt_one_iff : a⁻¹ < 1 ↔ 1 < a := by
  rw [← mul_lt_mul_iff_right a, inv_mul_self, one_mul]
#align right.inv_lt_one_iff Right.inv_lt_one_iff
#align right.neg_neg_iff Right.neg_neg_iff

/- warning: right.one_lt_inv_iff -> Right.one_lt_inv_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LT.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))))) (LT.lt.{u1} α _inst_2)] {a : α}, Iff (LT.lt.{u1} α _inst_2 (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))))) (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) a)) (LT.lt.{u1} α _inst_2 a (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LT.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.3196 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.3198 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.3196 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.3198)) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.3211 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.3213 : α) => LT.lt.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.3211 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.3213)] {a : α}, Iff (LT.lt.{u1} α _inst_2 (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (InvOneClass.toOne.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1)))))) (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1)))) a)) (LT.lt.{u1} α _inst_2 a (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (InvOneClass.toOne.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1)))))))
Case conversion may be inaccurate. Consider using '#align right.one_lt_inv_iff Right.one_lt_inv_iffₓ'. -/
/-- Uses `right` co(ntra)variant. -/
@[simp, to_additive Right.neg_pos_iff "Uses `right` co(ntra)variant."]
theorem Right.one_lt_inv_iff : 1 < a⁻¹ ↔ a < 1 := by
  rw [← mul_lt_mul_iff_right a, inv_mul_self, one_mul]
#align right.one_lt_inv_iff Right.one_lt_inv_iff
#align right.neg_pos_iff Right.neg_pos_iff

/- warning: inv_lt_iff_one_lt_mul -> inv_lt_iff_one_lt_mul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LT.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))))) (LT.lt.{u1} α _inst_2)] {a : α} {b : α}, Iff (LT.lt.{u1} α _inst_2 (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) a) b) (LT.lt.{u1} α _inst_2 (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) b a))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LT.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.3293 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.3295 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.3293 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.3295)) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.3308 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.3310 : α) => LT.lt.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.3308 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.3310)] {a : α} {b : α}, Iff (LT.lt.{u1} α _inst_2 (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1)))) a) b) (LT.lt.{u1} α _inst_2 (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (InvOneClass.toOne.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1)))))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) b a))
Case conversion may be inaccurate. Consider using '#align inv_lt_iff_one_lt_mul inv_lt_iff_one_lt_mulₓ'. -/
@[to_additive]
theorem inv_lt_iff_one_lt_mul : a⁻¹ < b ↔ 1 < b * a :=
  (mul_lt_mul_iff_right a).symm.trans <| by rw [inv_mul_self]
#align inv_lt_iff_one_lt_mul inv_lt_iff_one_lt_mul
#align neg_lt_iff_pos_add neg_lt_iff_pos_add

/- warning: lt_inv_iff_mul_lt_one -> lt_inv_iff_mul_lt_one is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LT.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))))) (LT.lt.{u1} α _inst_2)] {a : α} {b : α}, Iff (LT.lt.{u1} α _inst_2 a (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) b)) (LT.lt.{u1} α _inst_2 (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) a b) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LT.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.3395 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.3397 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.3395 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.3397)) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.3410 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.3412 : α) => LT.lt.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.3410 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.3412)] {a : α} {b : α}, Iff (LT.lt.{u1} α _inst_2 a (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1)))) b)) (LT.lt.{u1} α _inst_2 (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) a b) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (InvOneClass.toOne.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1)))))))
Case conversion may be inaccurate. Consider using '#align lt_inv_iff_mul_lt_one lt_inv_iff_mul_lt_oneₓ'. -/
@[to_additive]
theorem lt_inv_iff_mul_lt_one : a < b⁻¹ ↔ a * b < 1 :=
  (mul_lt_mul_iff_right b).symm.trans <| by rw [inv_mul_self]
#align lt_inv_iff_mul_lt_one lt_inv_iff_mul_lt_one
#align lt_neg_iff_add_neg lt_neg_iff_add_neg

/- warning: mul_inv_lt_iff_lt_mul -> mul_inv_lt_iff_lt_mul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LT.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))))) (LT.lt.{u1} α _inst_2)] {a : α} {b : α} {c : α}, Iff (LT.lt.{u1} α _inst_2 (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) a (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) b)) c) (LT.lt.{u1} α _inst_2 a (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) c b))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LT.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.3497 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.3499 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.3497 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.3499)) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.3512 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.3514 : α) => LT.lt.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.3512 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.3514)] {a : α} {b : α} {c : α}, Iff (LT.lt.{u1} α _inst_2 (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) a (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1)))) b)) c) (LT.lt.{u1} α _inst_2 a (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) c b))
Case conversion may be inaccurate. Consider using '#align mul_inv_lt_iff_lt_mul mul_inv_lt_iff_lt_mulₓ'. -/
@[simp, to_additive]
theorem mul_inv_lt_iff_lt_mul : a * b⁻¹ < c ↔ a < c * b := by
  rw [← mul_lt_mul_iff_right b, inv_mul_cancel_right]
#align mul_inv_lt_iff_lt_mul mul_inv_lt_iff_lt_mul
#align add_neg_lt_iff_lt_add add_neg_lt_iff_lt_add

/- warning: lt_mul_inv_iff_mul_lt -> lt_mul_inv_iff_mul_lt is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LT.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))))) (LT.lt.{u1} α _inst_2)] {a : α} {b : α} {c : α}, Iff (LT.lt.{u1} α _inst_2 c (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) a (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) b))) (LT.lt.{u1} α _inst_2 (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) c b) a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LT.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.3596 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.3598 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.3596 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.3598)) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.3611 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.3613 : α) => LT.lt.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.3611 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.3613)] {a : α} {b : α} {c : α}, Iff (LT.lt.{u1} α _inst_2 c (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) a (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1)))) b))) (LT.lt.{u1} α _inst_2 (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) c b) a)
Case conversion may be inaccurate. Consider using '#align lt_mul_inv_iff_mul_lt lt_mul_inv_iff_mul_ltₓ'. -/
@[simp, to_additive]
theorem lt_mul_inv_iff_mul_lt : c < a * b⁻¹ ↔ c * b < a :=
  (mul_lt_mul_iff_right b).symm.trans <| by rw [inv_mul_cancel_right]
#align lt_mul_inv_iff_mul_lt lt_mul_inv_iff_mul_lt
#align lt_add_neg_iff_add_lt lt_add_neg_iff_add_lt

/- warning: inv_mul_lt_one_iff_lt -> inv_mul_lt_one_iff_lt is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LT.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))))) (LT.lt.{u1} α _inst_2)] {a : α} {b : α}, Iff (LT.lt.{u1} α _inst_2 (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) a (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) b)) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)))))))) (LT.lt.{u1} α _inst_2 a b)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LT.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.3700 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.3702 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.3700 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.3702)) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.3715 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.3717 : α) => LT.lt.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.3715 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.3717)] {a : α} {b : α}, Iff (LT.lt.{u1} α _inst_2 (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) a (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1)))) b)) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (InvOneClass.toOne.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1))))))) (LT.lt.{u1} α _inst_2 a b)
Case conversion may be inaccurate. Consider using '#align inv_mul_lt_one_iff_lt inv_mul_lt_one_iff_ltₓ'. -/
@[simp, to_additive]
theorem inv_mul_lt_one_iff_lt : a * b⁻¹ < 1 ↔ a < b := by
  rw [← mul_lt_mul_iff_right b, inv_mul_cancel_right, one_mul]
#align inv_mul_lt_one_iff_lt inv_mul_lt_one_iff_lt
#align neg_add_neg_iff_lt neg_add_neg_iff_lt

/- warning: lt_mul_inv_iff_lt -> lt_mul_inv_iff_lt is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LT.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))))) (LT.lt.{u1} α _inst_2)] {a : α} {b : α}, Iff (LT.lt.{u1} α _inst_2 (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) a (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) b))) (LT.lt.{u1} α _inst_2 b a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LT.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.3798 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.3800 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.3798 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.3800)) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.3813 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.3815 : α) => LT.lt.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.3813 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.3815)] {a : α} {b : α}, Iff (LT.lt.{u1} α _inst_2 (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (InvOneClass.toOne.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1)))))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) a (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1)))) b))) (LT.lt.{u1} α _inst_2 b a)
Case conversion may be inaccurate. Consider using '#align lt_mul_inv_iff_lt lt_mul_inv_iff_ltₓ'. -/
@[to_additive]
theorem lt_mul_inv_iff_lt : 1 < a * b⁻¹ ↔ b < a := by
  rw [← mul_lt_mul_iff_right b, one_mul, inv_mul_cancel_right]
#align lt_mul_inv_iff_lt lt_mul_inv_iff_lt
#align lt_add_neg_iff_lt lt_add_neg_iff_lt

/- warning: mul_inv_lt_one_iff -> mul_inv_lt_one_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LT.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))))) (LT.lt.{u1} α _inst_2)] {a : α} {b : α}, Iff (LT.lt.{u1} α _inst_2 (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) b (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) a)) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)))))))) (LT.lt.{u1} α _inst_2 b a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LT.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.3896 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.3898 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.3896 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.3898)) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.3911 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.3913 : α) => LT.lt.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.3911 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.3913)] {a : α} {b : α}, Iff (LT.lt.{u1} α _inst_2 (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) b (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1)))) a)) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (InvOneClass.toOne.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1))))))) (LT.lt.{u1} α _inst_2 b a)
Case conversion may be inaccurate. Consider using '#align mul_inv_lt_one_iff mul_inv_lt_one_iffₓ'. -/
@[to_additive]
theorem mul_inv_lt_one_iff : b * a⁻¹ < 1 ↔ b < a :=
  trans mul_inv_lt_iff_lt_mul <| by rw [one_mul]
#align mul_inv_lt_one_iff mul_inv_lt_one_iff
#align add_neg_neg_iff add_neg_neg_iff

end TypeclassesRightLt

section TypeclassesLeftRightLe

variable [LE α] [CovariantClass α α (· * ·) (· ≤ ·)] [CovariantClass α α (swap (· * ·)) (· ≤ ·)]
  {a b c d : α}

/- warning: inv_le_inv_iff -> inv_le_inv_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LE.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)))))) (LE.le.{u1} α _inst_2)] [_inst_4 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))))) (LE.le.{u1} α _inst_2)] {a : α} {b : α}, Iff (LE.le.{u1} α _inst_2 (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) a) (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) b)) (LE.le.{u1} α _inst_2 b a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LE.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.4084 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.4086 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.4084 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.4086) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.4099 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.4101 : α) => LE.le.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.4099 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.4101)] [_inst_4 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.4121 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.4123 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.4121 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.4123)) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.4136 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.4138 : α) => LE.le.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.4136 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.4138)] {a : α} {b : α}, Iff (LE.le.{u1} α _inst_2 (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1)))) a) (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1)))) b)) (LE.le.{u1} α _inst_2 b a)
Case conversion may be inaccurate. Consider using '#align inv_le_inv_iff inv_le_inv_iffₓ'. -/
@[simp, to_additive]
theorem inv_le_inv_iff : a⁻¹ ≤ b⁻¹ ↔ b ≤ a :=
  by
  rw [← mul_le_mul_iff_left a, ← mul_le_mul_iff_right b]
  simp
#align inv_le_inv_iff inv_le_inv_iff
#align neg_le_neg_iff neg_le_neg_iff

/- warning: le_of_neg_le_neg -> le_of_neg_le_neg is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : AddGroup.{u1} α] [_inst_2 : LE.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α _inst_1)))))) (LE.le.{u1} α _inst_2)] [_inst_4 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α _inst_1))))))) (LE.le.{u1} α _inst_2)] {a : α} {b : α}, (LE.le.{u1} α _inst_2 (Neg.neg.{u1} α (SubNegMonoid.toHasNeg.{u1} α (AddGroup.toSubNegMonoid.{u1} α _inst_1)) a) (Neg.neg.{u1} α (SubNegMonoid.toHasNeg.{u1} α (AddGroup.toSubNegMonoid.{u1} α _inst_1)) b)) -> (LE.le.{u1} α _inst_2 b a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : AddGroup.{u1} α] [_inst_2 : LE.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.4084 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.4086 : α) => HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α _inst_1))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.4084 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.4086) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.4099 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.4101 : α) => LE.le.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.4099 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.4101)] [_inst_4 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.4121 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.4123 : α) => HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α _inst_1))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.4121 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.4123)) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.4136 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.4138 : α) => LE.le.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.4136 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.4138)] {a : α} {b : α}, (LE.le.{u1} α _inst_2 (Neg.neg.{u1} α (NegZeroClass.toNeg.{u1} α (SubNegZeroMonoid.toNegZeroClass.{u1} α (SubtractionMonoid.toSubNegZeroMonoid.{u1} α (AddGroup.toSubtractionMonoid.{u1} α _inst_1)))) a) (Neg.neg.{u1} α (NegZeroClass.toNeg.{u1} α (SubNegZeroMonoid.toNegZeroClass.{u1} α (SubtractionMonoid.toSubNegZeroMonoid.{u1} α (AddGroup.toSubtractionMonoid.{u1} α _inst_1)))) b)) -> (LE.le.{u1} α _inst_2 b a)
Case conversion may be inaccurate. Consider using '#align le_of_neg_le_neg le_of_neg_le_negₓ'. -/
alias neg_le_neg_iff ↔ le_of_neg_le_neg _
#align le_of_neg_le_neg le_of_neg_le_neg

/- warning: mul_inv_le_inv_mul_iff -> mul_inv_le_inv_mul_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LE.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)))))) (LE.le.{u1} α _inst_2)] [_inst_4 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))))) (LE.le.{u1} α _inst_2)] {a : α} {b : α} {c : α} {d : α}, Iff (LE.le.{u1} α _inst_2 (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) a (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) b)) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) d) c)) (LE.le.{u1} α _inst_2 (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) d a) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) c b))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LE.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.4224 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.4226 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.4224 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.4226) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.4239 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.4241 : α) => LE.le.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.4239 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.4241)] [_inst_4 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.4261 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.4263 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.4261 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.4263)) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.4276 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.4278 : α) => LE.le.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.4276 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.4278)] {a : α} {b : α} {c : α} {d : α}, Iff (LE.le.{u1} α _inst_2 (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) a (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1)))) b)) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1)))) d) c)) (LE.le.{u1} α _inst_2 (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) d a) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) c b))
Case conversion may be inaccurate. Consider using '#align mul_inv_le_inv_mul_iff mul_inv_le_inv_mul_iffₓ'. -/
@[to_additive]
theorem mul_inv_le_inv_mul_iff : a * b⁻¹ ≤ d⁻¹ * c ↔ d * a ≤ c * b := by
  rw [← mul_le_mul_iff_left d, ← mul_le_mul_iff_right b, mul_inv_cancel_left, mul_assoc,
    inv_mul_cancel_right]
#align mul_inv_le_inv_mul_iff mul_inv_le_inv_mul_iff
#align add_neg_le_neg_add_iff add_neg_le_neg_add_iff

/- warning: div_le_self_iff -> div_le_self_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LE.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)))))) (LE.le.{u1} α _inst_2)] [_inst_4 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))))) (LE.le.{u1} α _inst_2)] (a : α) {b : α}, Iff (LE.le.{u1} α _inst_2 (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toHasDiv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))) a b) a) (LE.le.{u1} α _inst_2 (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))))) b)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LE.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.4368 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.4370 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.4368 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.4370) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.4383 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.4385 : α) => LE.le.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.4383 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.4385)] (_inst_4 : α) {a : α}, Iff (LE.le.{u1} α _inst_2 (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toDiv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))) _inst_4 a) _inst_4) (LE.le.{u1} α _inst_2 (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (InvOneClass.toOne.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1)))))) a)
Case conversion may be inaccurate. Consider using '#align div_le_self_iff div_le_self_iffₓ'. -/
@[simp, to_additive]
theorem div_le_self_iff (a : α) {b : α} : a / b ≤ a ↔ 1 ≤ b := by simp [div_eq_mul_inv]
#align div_le_self_iff div_le_self_iff
#align sub_le_self_iff sub_le_self_iff

/- warning: le_div_self_iff -> le_div_self_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LE.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)))))) (LE.le.{u1} α _inst_2)] [_inst_4 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))))) (LE.le.{u1} α _inst_2)] (a : α) {b : α}, Iff (LE.le.{u1} α _inst_2 a (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toHasDiv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))) a b)) (LE.le.{u1} α _inst_2 b (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LE.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.4474 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.4476 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.4474 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.4476) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.4489 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.4491 : α) => LE.le.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.4489 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.4491)] (_inst_4 : α) {a : α}, Iff (LE.le.{u1} α _inst_2 _inst_4 (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toDiv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))) _inst_4 a)) (LE.le.{u1} α _inst_2 a (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (InvOneClass.toOne.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1)))))))
Case conversion may be inaccurate. Consider using '#align le_div_self_iff le_div_self_iffₓ'. -/
@[simp, to_additive]
theorem le_div_self_iff (a : α) {b : α} : a ≤ a / b ↔ b ≤ 1 := by simp [div_eq_mul_inv]
#align le_div_self_iff le_div_self_iff
#align le_sub_self_iff le_sub_self_iff

/- warning: sub_le_self -> sub_le_self is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : AddGroup.{u1} α] [_inst_2 : LE.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α _inst_1)))))) (LE.le.{u1} α _inst_2)] [_inst_4 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α _inst_1))))))) (LE.le.{u1} α _inst_2)] (a : α) {b : α}, (LE.le.{u1} α _inst_2 (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α _inst_1))))))) b) -> (LE.le.{u1} α _inst_2 (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α (SubNegMonoid.toHasSub.{u1} α (AddGroup.toSubNegMonoid.{u1} α _inst_1))) a b) a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : AddGroup.{u1} α] [_inst_2 : LE.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.4368 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.4370 : α) => HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α _inst_1))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.4368 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.4370) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.4383 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.4385 : α) => LE.le.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.4383 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.4385)] (_inst_4 : α) {a : α}, (LE.le.{u1} α _inst_2 (OfNat.ofNat.{u1} α 0 (Zero.toOfNat0.{u1} α (NegZeroClass.toZero.{u1} α (SubNegZeroMonoid.toNegZeroClass.{u1} α (SubtractionMonoid.toSubNegZeroMonoid.{u1} α (AddGroup.toSubtractionMonoid.{u1} α _inst_1)))))) a) -> (LE.le.{u1} α _inst_2 (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α (SubNegMonoid.toSub.{u1} α (AddGroup.toSubNegMonoid.{u1} α _inst_1))) _inst_4 a) _inst_4)
Case conversion may be inaccurate. Consider using '#align sub_le_self sub_le_selfₓ'. -/
alias sub_le_self_iff ↔ _ sub_le_self
#align sub_le_self sub_le_self

end TypeclassesLeftRightLe

section TypeclassesLeftRightLt

variable [LT α] [CovariantClass α α (· * ·) (· < ·)] [CovariantClass α α (swap (· * ·)) (· < ·)]
  {a b c d : α}

/- warning: inv_lt_inv_iff -> inv_lt_inv_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LT.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)))))) (LT.lt.{u1} α _inst_2)] [_inst_4 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))))) (LT.lt.{u1} α _inst_2)] {a : α} {b : α}, Iff (LT.lt.{u1} α _inst_2 (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) a) (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) b)) (LT.lt.{u1} α _inst_2 b a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LT.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.4674 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.4676 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.4674 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.4676) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.4689 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.4691 : α) => LT.lt.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.4689 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.4691)] [_inst_4 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.4711 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.4713 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.4711 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.4713)) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.4726 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.4728 : α) => LT.lt.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.4726 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.4728)] {a : α} {b : α}, Iff (LT.lt.{u1} α _inst_2 (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1)))) a) (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1)))) b)) (LT.lt.{u1} α _inst_2 b a)
Case conversion may be inaccurate. Consider using '#align inv_lt_inv_iff inv_lt_inv_iffₓ'. -/
@[simp, to_additive]
theorem inv_lt_inv_iff : a⁻¹ < b⁻¹ ↔ b < a :=
  by
  rw [← mul_lt_mul_iff_left a, ← mul_lt_mul_iff_right b]
  simp
#align inv_lt_inv_iff inv_lt_inv_iff
#align neg_lt_neg_iff neg_lt_neg_iff

/- warning: inv_lt' -> inv_lt' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LT.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)))))) (LT.lt.{u1} α _inst_2)] [_inst_4 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))))) (LT.lt.{u1} α _inst_2)] {a : α} {b : α}, Iff (LT.lt.{u1} α _inst_2 (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) a) b) (LT.lt.{u1} α _inst_2 (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) b) a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LT.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.4812 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.4814 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.4812 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.4814) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.4827 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.4829 : α) => LT.lt.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.4827 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.4829)] [_inst_4 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.4849 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.4851 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.4849 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.4851)) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.4864 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.4866 : α) => LT.lt.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.4864 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.4866)] {a : α} {b : α}, Iff (LT.lt.{u1} α _inst_2 (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1)))) a) b) (LT.lt.{u1} α _inst_2 (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1)))) b) a)
Case conversion may be inaccurate. Consider using '#align inv_lt' inv_lt'ₓ'. -/
@[to_additive neg_lt]
theorem inv_lt' : a⁻¹ < b ↔ b⁻¹ < a := by rw [← inv_lt_inv_iff, inv_inv]
#align inv_lt' inv_lt'
#align neg_lt neg_lt

/- warning: lt_inv' -> lt_inv' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LT.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)))))) (LT.lt.{u1} α _inst_2)] [_inst_4 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))))) (LT.lt.{u1} α _inst_2)] {a : α} {b : α}, Iff (LT.lt.{u1} α _inst_2 a (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) b)) (LT.lt.{u1} α _inst_2 b (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) a))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LT.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.4943 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.4945 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.4943 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.4945) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.4958 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.4960 : α) => LT.lt.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.4958 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.4960)] [_inst_4 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.4980 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.4982 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.4980 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.4982)) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.4995 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.4997 : α) => LT.lt.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.4995 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.4997)] {a : α} {b : α}, Iff (LT.lt.{u1} α _inst_2 a (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1)))) b)) (LT.lt.{u1} α _inst_2 b (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1)))) a))
Case conversion may be inaccurate. Consider using '#align lt_inv' lt_inv'ₓ'. -/
@[to_additive lt_neg]
theorem lt_inv' : a < b⁻¹ ↔ b < a⁻¹ := by rw [← inv_lt_inv_iff, inv_inv]
#align lt_inv' lt_inv'
#align lt_neg lt_neg

/- warning: lt_inv_of_lt_inv -> lt_inv_of_lt_inv is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LT.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)))))) (LT.lt.{u1} α _inst_2)] [_inst_4 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))))) (LT.lt.{u1} α _inst_2)] {a : α} {b : α}, (LT.lt.{u1} α _inst_2 a (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) b)) -> (LT.lt.{u1} α _inst_2 b (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) a))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LT.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.4943 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.4945 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.4943 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.4945) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.4958 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.4960 : α) => LT.lt.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.4958 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.4960)] [_inst_4 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.4980 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.4982 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.4980 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.4982)) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.4995 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.4997 : α) => LT.lt.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.4995 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.4997)] {a : α} {b : α}, (LT.lt.{u1} α _inst_2 a (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1)))) b)) -> (LT.lt.{u1} α _inst_2 b (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1)))) a))
Case conversion may be inaccurate. Consider using '#align lt_inv_of_lt_inv lt_inv_of_lt_invₓ'. -/
alias lt_inv' ↔ lt_inv_of_lt_inv _
#align lt_inv_of_lt_inv lt_inv_of_lt_inv

attribute [to_additive] lt_inv_of_lt_inv

/- warning: inv_lt_of_inv_lt' -> inv_lt_of_inv_lt' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LT.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)))))) (LT.lt.{u1} α _inst_2)] [_inst_4 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))))) (LT.lt.{u1} α _inst_2)] {a : α} {b : α}, (LT.lt.{u1} α _inst_2 (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) a) b) -> (LT.lt.{u1} α _inst_2 (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) b) a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LT.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.4812 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.4814 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.4812 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.4814) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.4827 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.4829 : α) => LT.lt.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.4827 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.4829)] [_inst_4 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.4849 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.4851 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.4849 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.4851)) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.4864 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.4866 : α) => LT.lt.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.4864 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.4866)] {a : α} {b : α}, (LT.lt.{u1} α _inst_2 (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1)))) a) b) -> (LT.lt.{u1} α _inst_2 (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1)))) b) a)
Case conversion may be inaccurate. Consider using '#align inv_lt_of_inv_lt' inv_lt_of_inv_lt'ₓ'. -/
alias inv_lt' ↔ inv_lt_of_inv_lt' _
#align inv_lt_of_inv_lt' inv_lt_of_inv_lt'

attribute [to_additive neg_lt_of_neg_lt] inv_lt_of_inv_lt'

/- warning: mul_inv_lt_inv_mul_iff -> mul_inv_lt_inv_mul_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LT.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)))))) (LT.lt.{u1} α _inst_2)] [_inst_4 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))))) (LT.lt.{u1} α _inst_2)] {a : α} {b : α} {c : α} {d : α}, Iff (LT.lt.{u1} α _inst_2 (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) a (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) b)) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) d) c)) (LT.lt.{u1} α _inst_2 (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) d a) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) c b))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LT.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.5082 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.5084 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.5082 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.5084) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.5097 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.5099 : α) => LT.lt.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.5097 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.5099)] [_inst_4 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.5119 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.5121 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.5119 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.5121)) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.5134 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.5136 : α) => LT.lt.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.5134 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.5136)] {a : α} {b : α} {c : α} {d : α}, Iff (LT.lt.{u1} α _inst_2 (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) a (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1)))) b)) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1)))) d) c)) (LT.lt.{u1} α _inst_2 (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) d a) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) c b))
Case conversion may be inaccurate. Consider using '#align mul_inv_lt_inv_mul_iff mul_inv_lt_inv_mul_iffₓ'. -/
@[to_additive]
theorem mul_inv_lt_inv_mul_iff : a * b⁻¹ < d⁻¹ * c ↔ d * a < c * b := by
  rw [← mul_lt_mul_iff_left d, ← mul_lt_mul_iff_right b, mul_inv_cancel_left, mul_assoc,
    inv_mul_cancel_right]
#align mul_inv_lt_inv_mul_iff mul_inv_lt_inv_mul_iff
#align add_neg_lt_neg_add_iff add_neg_lt_neg_add_iff

/- warning: div_lt_self_iff -> div_lt_self_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LT.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)))))) (LT.lt.{u1} α _inst_2)] [_inst_4 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))))) (LT.lt.{u1} α _inst_2)] (a : α) {b : α}, Iff (LT.lt.{u1} α _inst_2 (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toHasDiv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))) a b) a) (LT.lt.{u1} α _inst_2 (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))))) b)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LT.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.5226 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.5228 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.5226 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.5228) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.5241 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.5243 : α) => LT.lt.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.5241 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.5243)] (_inst_4 : α) {a : α}, Iff (LT.lt.{u1} α _inst_2 (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toDiv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))) _inst_4 a) _inst_4) (LT.lt.{u1} α _inst_2 (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (InvOneClass.toOne.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1)))))) a)
Case conversion may be inaccurate. Consider using '#align div_lt_self_iff div_lt_self_iffₓ'. -/
@[simp, to_additive]
theorem div_lt_self_iff (a : α) {b : α} : a / b < a ↔ 1 < b := by simp [div_eq_mul_inv]
#align div_lt_self_iff div_lt_self_iff
#align sub_lt_self_iff sub_lt_self_iff

/- warning: sub_lt_self -> sub_lt_self is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : AddGroup.{u1} α] [_inst_2 : LT.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α _inst_1)))))) (LT.lt.{u1} α _inst_2)] [_inst_4 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α _inst_1))))))) (LT.lt.{u1} α _inst_2)] (a : α) {b : α}, (LT.lt.{u1} α _inst_2 (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α _inst_1))))))) b) -> (LT.lt.{u1} α _inst_2 (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α (SubNegMonoid.toHasSub.{u1} α (AddGroup.toSubNegMonoid.{u1} α _inst_1))) a b) a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : AddGroup.{u1} α] [_inst_2 : LT.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.5226 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.5228 : α) => HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α _inst_1))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.5226 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.5228) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.5241 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.5243 : α) => LT.lt.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.5241 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.5243)] (_inst_4 : α) {a : α}, (LT.lt.{u1} α _inst_2 (OfNat.ofNat.{u1} α 0 (Zero.toOfNat0.{u1} α (NegZeroClass.toZero.{u1} α (SubNegZeroMonoid.toNegZeroClass.{u1} α (SubtractionMonoid.toSubNegZeroMonoid.{u1} α (AddGroup.toSubtractionMonoid.{u1} α _inst_1)))))) a) -> (LT.lt.{u1} α _inst_2 (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α (SubNegMonoid.toSub.{u1} α (AddGroup.toSubNegMonoid.{u1} α _inst_1))) _inst_4 a) _inst_4)
Case conversion may be inaccurate. Consider using '#align sub_lt_self sub_lt_selfₓ'. -/
alias sub_lt_self_iff ↔ _ sub_lt_self
#align sub_lt_self sub_lt_self

end TypeclassesLeftRightLt

section PreOrder

variable [Preorder α]

section LeftLe

variable [CovariantClass α α (· * ·) (· ≤ ·)] {a : α}

/- warning: left.inv_le_self -> Left.inv_le_self is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)))))) (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2))] {a : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))))) a) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) a) a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.5394 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.5396 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.5394 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.5396) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.5409 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.5411 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.5409 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.5411)] {a : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (InvOneClass.toOne.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1)))))) a) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1)))) a) a)
Case conversion may be inaccurate. Consider using '#align left.inv_le_self Left.inv_le_selfₓ'. -/
@[to_additive]
theorem Left.inv_le_self (h : 1 ≤ a) : a⁻¹ ≤ a :=
  le_trans (Left.inv_le_one_iff.mpr h) h
#align left.inv_le_self Left.inv_le_self
#align left.neg_le_self Left.neg_le_self

/- warning: neg_le_self -> neg_le_self is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : AddGroup.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α _inst_1)))))) (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2))] {a : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α _inst_1))))))) a) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) (Neg.neg.{u1} α (SubNegMonoid.toHasNeg.{u1} α (AddGroup.toSubNegMonoid.{u1} α _inst_1)) a) a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : AddGroup.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.5394 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.5396 : α) => HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α _inst_1))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.5394 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.5396) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.5409 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.5411 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.5409 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.5411)] {a : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) (OfNat.ofNat.{u1} α 0 (Zero.toOfNat0.{u1} α (NegZeroClass.toZero.{u1} α (SubNegZeroMonoid.toNegZeroClass.{u1} α (SubtractionMonoid.toSubNegZeroMonoid.{u1} α (AddGroup.toSubtractionMonoid.{u1} α _inst_1)))))) a) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) (Neg.neg.{u1} α (NegZeroClass.toNeg.{u1} α (SubNegZeroMonoid.toNegZeroClass.{u1} α (SubtractionMonoid.toSubNegZeroMonoid.{u1} α (AddGroup.toSubtractionMonoid.{u1} α _inst_1)))) a) a)
Case conversion may be inaccurate. Consider using '#align neg_le_self neg_le_selfₓ'. -/
alias Left.neg_le_self ← neg_le_self
#align neg_le_self neg_le_self

/- warning: left.self_le_inv -> Left.self_le_inv is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)))))) (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2))] {a : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) a (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)))))))) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) a (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) a))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.5463 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.5465 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.5463 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.5465) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.5478 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.5480 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.5478 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.5480)] {a : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) a (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (InvOneClass.toOne.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1))))))) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) a (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1)))) a))
Case conversion may be inaccurate. Consider using '#align left.self_le_inv Left.self_le_invₓ'. -/
@[to_additive]
theorem Left.self_le_inv (h : a ≤ 1) : a ≤ a⁻¹ :=
  le_trans h (Left.one_le_inv_iff.mpr h)
#align left.self_le_inv Left.self_le_inv
#align left.self_le_neg Left.self_le_neg

end LeftLe

section LeftLt

variable [CovariantClass α α (· * ·) (· < ·)] {a : α}

/- warning: left.inv_lt_self -> Left.inv_lt_self is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)))))) (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2))] {a : α}, (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))))) a) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) a) a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.5577 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.5579 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.5577 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.5579) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.5592 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.5594 : α) => LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.5592 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.5594)] {a : α}, (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (InvOneClass.toOne.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1)))))) a) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1)))) a) a)
Case conversion may be inaccurate. Consider using '#align left.inv_lt_self Left.inv_lt_selfₓ'. -/
@[to_additive]
theorem Left.inv_lt_self (h : 1 < a) : a⁻¹ < a :=
  (Left.inv_lt_one_iff.mpr h).trans h
#align left.inv_lt_self Left.inv_lt_self
#align left.neg_lt_self Left.neg_lt_self

/- warning: neg_lt_self -> neg_lt_self is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : AddGroup.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α _inst_1)))))) (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2))] {a : α}, (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α _inst_1))))))) a) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (Neg.neg.{u1} α (SubNegMonoid.toHasNeg.{u1} α (AddGroup.toSubNegMonoid.{u1} α _inst_1)) a) a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : AddGroup.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.5577 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.5579 : α) => HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α _inst_1))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.5577 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.5579) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.5592 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.5594 : α) => LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.5592 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.5594)] {a : α}, (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (OfNat.ofNat.{u1} α 0 (Zero.toOfNat0.{u1} α (NegZeroClass.toZero.{u1} α (SubNegZeroMonoid.toNegZeroClass.{u1} α (SubtractionMonoid.toSubNegZeroMonoid.{u1} α (AddGroup.toSubtractionMonoid.{u1} α _inst_1)))))) a) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (Neg.neg.{u1} α (NegZeroClass.toNeg.{u1} α (SubNegZeroMonoid.toNegZeroClass.{u1} α (SubtractionMonoid.toSubNegZeroMonoid.{u1} α (AddGroup.toSubtractionMonoid.{u1} α _inst_1)))) a) a)
Case conversion may be inaccurate. Consider using '#align neg_lt_self neg_lt_selfₓ'. -/
alias Left.neg_lt_self ← neg_lt_self
#align neg_lt_self neg_lt_self

/- warning: left.self_lt_inv -> Left.self_lt_inv is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)))))) (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2))] {a : α}, (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) a (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)))))))) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) a (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) a))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.5646 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.5648 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.5646 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.5648) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.5661 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.5663 : α) => LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.5661 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.5663)] {a : α}, (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) a (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (InvOneClass.toOne.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1))))))) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) a (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1)))) a))
Case conversion may be inaccurate. Consider using '#align left.self_lt_inv Left.self_lt_invₓ'. -/
@[to_additive]
theorem Left.self_lt_inv (h : a < 1) : a < a⁻¹ :=
  lt_trans h (Left.one_lt_inv_iff.mpr h)
#align left.self_lt_inv Left.self_lt_inv
#align left.self_lt_neg Left.self_lt_neg

end LeftLt

section RightLe

variable [CovariantClass α α (swap (· * ·)) (· ≤ ·)] {a : α}

/- warning: right.inv_le_self -> Right.inv_le_self is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))))) (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2))] {a : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))))) a) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) a) a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.5766 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.5768 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.5766 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.5768)) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.5781 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.5783 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.5781 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.5783)] {a : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (InvOneClass.toOne.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1)))))) a) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1)))) a) a)
Case conversion may be inaccurate. Consider using '#align right.inv_le_self Right.inv_le_selfₓ'. -/
@[to_additive]
theorem Right.inv_le_self (h : 1 ≤ a) : a⁻¹ ≤ a :=
  le_trans (Right.inv_le_one_iff.mpr h) h
#align right.inv_le_self Right.inv_le_self
#align right.neg_le_self Right.neg_le_self

/- warning: right.self_le_inv -> Right.self_le_inv is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))))) (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2))] {a : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) a (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)))))))) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) a (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) a))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.5836 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.5838 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.5836 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.5838)) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.5851 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.5853 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.5851 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.5853)] {a : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) a (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (InvOneClass.toOne.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1))))))) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) a (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1)))) a))
Case conversion may be inaccurate. Consider using '#align right.self_le_inv Right.self_le_invₓ'. -/
@[to_additive]
theorem Right.self_le_inv (h : a ≤ 1) : a ≤ a⁻¹ :=
  le_trans h (Right.one_le_inv_iff.mpr h)
#align right.self_le_inv Right.self_le_inv
#align right.self_le_neg Right.self_le_neg

end RightLe

section RightLt

variable [CovariantClass α α (swap (· * ·)) (· < ·)] {a : α}

/- warning: right.inv_lt_self -> Right.inv_lt_self is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))))) (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2))] {a : α}, (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))))) a) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) a) a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.5956 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.5958 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.5956 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.5958)) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.5971 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.5973 : α) => LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.5971 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.5973)] {a : α}, (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (InvOneClass.toOne.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1)))))) a) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1)))) a) a)
Case conversion may be inaccurate. Consider using '#align right.inv_lt_self Right.inv_lt_selfₓ'. -/
@[to_additive]
theorem Right.inv_lt_self (h : 1 < a) : a⁻¹ < a :=
  (Right.inv_lt_one_iff.mpr h).trans h
#align right.inv_lt_self Right.inv_lt_self
#align right.neg_lt_self Right.neg_lt_self

/- warning: right.self_lt_inv -> Right.self_lt_inv is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))))) (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2))] {a : α}, (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) a (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)))))))) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) a (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) a))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.6026 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.6028 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.6026 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.6028)) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.6041 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.6043 : α) => LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.6041 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.6043)] {a : α}, (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) a (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (InvOneClass.toOne.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1))))))) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) a (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1)))) a))
Case conversion may be inaccurate. Consider using '#align right.self_lt_inv Right.self_lt_invₓ'. -/
@[to_additive]
theorem Right.self_lt_inv (h : a < 1) : a < a⁻¹ :=
  lt_trans h (Right.one_lt_inv_iff.mpr h)
#align right.self_lt_inv Right.self_lt_inv
#align right.self_lt_neg Right.self_lt_neg

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
  forall {α : Type.{u1}} [_inst_1 : CommGroup.{u1} α] [_inst_2 : LE.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.6153 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.6155 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1)))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.6153 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.6155) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.6168 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.6170 : α) => LE.le.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.6168 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.6170)] {a : α} {b : α} {c : α}, Iff (LE.le.{u1} α _inst_2 (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1)))))) (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α (CommGroup.toDivisionCommMonoid.{u1} α _inst_1))))) c) a) b) (LE.le.{u1} α _inst_2 a (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1)))))) b c))
Case conversion may be inaccurate. Consider using '#align inv_mul_le_iff_le_mul' inv_mul_le_iff_le_mul'ₓ'. -/
@[to_additive]
theorem inv_mul_le_iff_le_mul' : c⁻¹ * a ≤ b ↔ a ≤ b * c := by rw [inv_mul_le_iff_le_mul, mul_comm]
#align inv_mul_le_iff_le_mul' inv_mul_le_iff_le_mul'
#align neg_add_le_iff_le_add' neg_add_le_iff_le_add'

/- warning: mul_inv_le_iff_le_mul' -> mul_inv_le_iff_le_mul' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CommGroup.{u1} α] [_inst_2 : LE.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1))))))) (LE.le.{u1} α _inst_2)] {a : α} {b : α} {c : α}, Iff (LE.le.{u1} α _inst_2 (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1)))))) a (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1))) b)) c) (LE.le.{u1} α _inst_2 a (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1)))))) b c))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CommGroup.{u1} α] [_inst_2 : LE.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.6249 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.6251 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1)))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.6249 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.6251) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.6264 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.6266 : α) => LE.le.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.6264 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.6266)] {a : α} {b : α} {c : α}, Iff (LE.le.{u1} α _inst_2 (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1)))))) a (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α (CommGroup.toDivisionCommMonoid.{u1} α _inst_1))))) b)) c) (LE.le.{u1} α _inst_2 a (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1)))))) b c))
Case conversion may be inaccurate. Consider using '#align mul_inv_le_iff_le_mul' mul_inv_le_iff_le_mul'ₓ'. -/
@[simp, to_additive]
theorem mul_inv_le_iff_le_mul' : a * b⁻¹ ≤ c ↔ a ≤ b * c := by
  rw [← inv_mul_le_iff_le_mul, mul_comm]
#align mul_inv_le_iff_le_mul' mul_inv_le_iff_le_mul'
#align add_neg_le_iff_le_add' add_neg_le_iff_le_add'

/- warning: mul_inv_le_mul_inv_iff' -> mul_inv_le_mul_inv_iff' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CommGroup.{u1} α] [_inst_2 : LE.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1))))))) (LE.le.{u1} α _inst_2)] {a : α} {b : α} {c : α} {d : α}, Iff (LE.le.{u1} α _inst_2 (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1)))))) a (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1))) b)) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1)))))) c (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1))) d))) (LE.le.{u1} α _inst_2 (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1)))))) a d) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1)))))) c b))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CommGroup.{u1} α] [_inst_2 : LE.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.6345 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.6347 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1)))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.6345 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.6347) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.6360 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.6362 : α) => LE.le.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.6360 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.6362)] {a : α} {b : α} {c : α} {d : α}, Iff (LE.le.{u1} α _inst_2 (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1)))))) a (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α (CommGroup.toDivisionCommMonoid.{u1} α _inst_1))))) b)) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1)))))) c (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α (CommGroup.toDivisionCommMonoid.{u1} α _inst_1))))) d))) (LE.le.{u1} α _inst_2 (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1)))))) a d) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1)))))) c b))
Case conversion may be inaccurate. Consider using '#align mul_inv_le_mul_inv_iff' mul_inv_le_mul_inv_iff'ₓ'. -/
@[to_additive add_neg_le_add_neg_iff]
theorem mul_inv_le_mul_inv_iff' : a * b⁻¹ ≤ c * d⁻¹ ↔ a * d ≤ c * b := by
  rw [mul_comm c, mul_inv_le_inv_mul_iff, mul_comm]
#align mul_inv_le_mul_inv_iff' mul_inv_le_mul_inv_iff'
#align add_neg_le_add_neg_iff add_neg_le_add_neg_iff

end LE

section LT

variable [LT α] [CovariantClass α α (· * ·) (· < ·)] {a b c d : α}

/- warning: inv_mul_lt_iff_lt_mul' -> inv_mul_lt_iff_lt_mul' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CommGroup.{u1} α] [_inst_2 : LT.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1))))))) (LT.lt.{u1} α _inst_2)] {a : α} {b : α} {c : α}, Iff (LT.lt.{u1} α _inst_2 (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1)))))) (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1))) c) a) b) (LT.lt.{u1} α _inst_2 a (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1)))))) b c))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CommGroup.{u1} α] [_inst_2 : LT.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.6503 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.6505 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1)))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.6503 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.6505) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.6518 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.6520 : α) => LT.lt.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.6518 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.6520)] {a : α} {b : α} {c : α}, Iff (LT.lt.{u1} α _inst_2 (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1)))))) (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α (CommGroup.toDivisionCommMonoid.{u1} α _inst_1))))) c) a) b) (LT.lt.{u1} α _inst_2 a (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1)))))) b c))
Case conversion may be inaccurate. Consider using '#align inv_mul_lt_iff_lt_mul' inv_mul_lt_iff_lt_mul'ₓ'. -/
@[to_additive]
theorem inv_mul_lt_iff_lt_mul' : c⁻¹ * a < b ↔ a < b * c := by rw [inv_mul_lt_iff_lt_mul, mul_comm]
#align inv_mul_lt_iff_lt_mul' inv_mul_lt_iff_lt_mul'
#align neg_add_lt_iff_lt_add' neg_add_lt_iff_lt_add'

/- warning: mul_inv_lt_iff_le_mul' -> mul_inv_lt_iff_le_mul' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CommGroup.{u1} α] [_inst_2 : LT.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1))))))) (LT.lt.{u1} α _inst_2)] {a : α} {b : α} {c : α}, Iff (LT.lt.{u1} α _inst_2 (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1)))))) a (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1))) b)) c) (LT.lt.{u1} α _inst_2 a (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1)))))) b c))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CommGroup.{u1} α] [_inst_2 : LT.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.6599 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.6601 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1)))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.6599 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.6601) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.6614 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.6616 : α) => LT.lt.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.6614 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.6616)] {a : α} {b : α} {c : α}, Iff (LT.lt.{u1} α _inst_2 (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1)))))) a (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α (CommGroup.toDivisionCommMonoid.{u1} α _inst_1))))) b)) c) (LT.lt.{u1} α _inst_2 a (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1)))))) b c))
Case conversion may be inaccurate. Consider using '#align mul_inv_lt_iff_le_mul' mul_inv_lt_iff_le_mul'ₓ'. -/
@[simp, to_additive]
theorem mul_inv_lt_iff_le_mul' : a * b⁻¹ < c ↔ a < b * c := by
  rw [← inv_mul_lt_iff_lt_mul, mul_comm]
#align mul_inv_lt_iff_le_mul' mul_inv_lt_iff_le_mul'
#align add_neg_lt_iff_le_add' add_neg_lt_iff_le_add'

/- warning: mul_inv_lt_mul_inv_iff' -> mul_inv_lt_mul_inv_iff' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CommGroup.{u1} α] [_inst_2 : LT.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1))))))) (LT.lt.{u1} α _inst_2)] {a : α} {b : α} {c : α} {d : α}, Iff (LT.lt.{u1} α _inst_2 (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1)))))) a (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1))) b)) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1)))))) c (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1))) d))) (LT.lt.{u1} α _inst_2 (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1)))))) a d) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1)))))) c b))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CommGroup.{u1} α] [_inst_2 : LT.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.6695 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.6697 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1)))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.6695 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.6697) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.6710 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.6712 : α) => LT.lt.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.6710 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.6712)] {a : α} {b : α} {c : α} {d : α}, Iff (LT.lt.{u1} α _inst_2 (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1)))))) a (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α (CommGroup.toDivisionCommMonoid.{u1} α _inst_1))))) b)) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1)))))) c (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α (CommGroup.toDivisionCommMonoid.{u1} α _inst_1))))) d))) (LT.lt.{u1} α _inst_2 (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1)))))) a d) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1)))))) c b))
Case conversion may be inaccurate. Consider using '#align mul_inv_lt_mul_inv_iff' mul_inv_lt_mul_inv_iff'ₓ'. -/
@[to_additive add_neg_lt_add_neg_iff]
theorem mul_inv_lt_mul_inv_iff' : a * b⁻¹ < c * d⁻¹ ↔ a * d < c * b := by
  rw [mul_comm c, mul_inv_lt_inv_mul_iff, mul_comm]
#align mul_inv_lt_mul_inv_iff' mul_inv_lt_mul_inv_iff'
#align add_neg_lt_add_neg_iff add_neg_lt_add_neg_iff

end LT

end CommGroup

/- warning: one_le_of_inv_le_one -> one_le_of_inv_le_one is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LE.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)))))) (LE.le.{u1} α _inst_2)] {a : α}, (LE.le.{u1} α _inst_2 (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) a) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)))))))) -> (LE.le.{u1} α _inst_2 (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))))) a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LE.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.446 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.448 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.446 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.448) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.461 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.463 : α) => LE.le.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.461 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.463)] {a : α}, (LE.le.{u1} α _inst_2 (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1)))) a) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (InvOneClass.toOne.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1))))))) -> (LE.le.{u1} α _inst_2 (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (InvOneClass.toOne.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1)))))) a)
Case conversion may be inaccurate. Consider using '#align one_le_of_inv_le_one one_le_of_inv_le_oneₓ'. -/
alias Left.inv_le_one_iff ↔ one_le_of_inv_le_one _
#align one_le_of_inv_le_one one_le_of_inv_le_one

attribute [to_additive] one_le_of_inv_le_one

/- warning: le_one_of_one_le_inv -> le_one_of_one_le_inv is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LE.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)))))) (LE.le.{u1} α _inst_2)] {a : α}, (LE.le.{u1} α _inst_2 (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))))) (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) a)) -> (LE.le.{u1} α _inst_2 a (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LE.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.547 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.549 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.547 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.549) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.562 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.564 : α) => LE.le.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.562 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.564)] {a : α}, (LE.le.{u1} α _inst_2 (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (InvOneClass.toOne.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1)))))) (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1)))) a)) -> (LE.le.{u1} α _inst_2 a (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (InvOneClass.toOne.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1)))))))
Case conversion may be inaccurate. Consider using '#align le_one_of_one_le_inv le_one_of_one_le_invₓ'. -/
alias Left.one_le_inv_iff ↔ le_one_of_one_le_inv _
#align le_one_of_one_le_inv le_one_of_one_le_inv

attribute [to_additive nonpos_of_neg_nonneg] le_one_of_one_le_inv

/- warning: lt_of_inv_lt_inv -> lt_of_inv_lt_inv is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LT.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)))))) (LT.lt.{u1} α _inst_2)] [_inst_4 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))))) (LT.lt.{u1} α _inst_2)] {a : α} {b : α}, (LT.lt.{u1} α _inst_2 (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) a) (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) b)) -> (LT.lt.{u1} α _inst_2 b a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LT.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.4674 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.4676 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.4674 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.4676) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.4689 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.4691 : α) => LT.lt.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.4689 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.4691)] [_inst_4 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.4711 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.4713 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.4711 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.4713)) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.4726 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.4728 : α) => LT.lt.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.4726 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.4728)] {a : α} {b : α}, (LT.lt.{u1} α _inst_2 (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1)))) a) (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1)))) b)) -> (LT.lt.{u1} α _inst_2 b a)
Case conversion may be inaccurate. Consider using '#align lt_of_inv_lt_inv lt_of_inv_lt_invₓ'. -/
alias inv_lt_inv_iff ↔ lt_of_inv_lt_inv _
#align lt_of_inv_lt_inv lt_of_inv_lt_inv

attribute [to_additive] lt_of_inv_lt_inv

/- warning: one_lt_of_inv_lt_one -> one_lt_of_inv_lt_one is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LT.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)))))) (LT.lt.{u1} α _inst_2)] {a : α}, (LT.lt.{u1} α _inst_2 (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) a) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)))))))) -> (LT.lt.{u1} α _inst_2 (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))))) a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LT.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.1388 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.1390 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.1388 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.1390) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.1403 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.1405 : α) => LT.lt.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.1403 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.1405)] {a : α}, (LT.lt.{u1} α _inst_2 (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1)))) a) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (InvOneClass.toOne.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1))))))) -> (LT.lt.{u1} α _inst_2 (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (InvOneClass.toOne.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1)))))) a)
Case conversion may be inaccurate. Consider using '#align one_lt_of_inv_lt_one one_lt_of_inv_lt_oneₓ'. -/
alias Left.inv_lt_one_iff ↔ one_lt_of_inv_lt_one _
#align one_lt_of_inv_lt_one one_lt_of_inv_lt_one

attribute [to_additive] one_lt_of_inv_lt_one

/- warning: inv_lt_one_iff_one_lt -> inv_lt_one_iff_one_lt is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LT.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)))))) (LT.lt.{u1} α _inst_2)] {a : α}, Iff (LT.lt.{u1} α _inst_2 (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) a) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)))))))) (LT.lt.{u1} α _inst_2 (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))))) a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LT.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.1388 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.1390 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.1388 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.1390) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.1403 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.1405 : α) => LT.lt.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.1403 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.1405)] {a : α}, Iff (LT.lt.{u1} α _inst_2 (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1)))) a) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (InvOneClass.toOne.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1))))))) (LT.lt.{u1} α _inst_2 (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (InvOneClass.toOne.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1)))))) a)
Case conversion may be inaccurate. Consider using '#align inv_lt_one_iff_one_lt inv_lt_one_iff_one_ltₓ'. -/
alias Left.inv_lt_one_iff ← inv_lt_one_iff_one_lt
#align inv_lt_one_iff_one_lt inv_lt_one_iff_one_lt

attribute [to_additive] inv_lt_one_iff_one_lt

/- warning: inv_lt_one' -> inv_lt_one' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LT.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)))))) (LT.lt.{u1} α _inst_2)] {a : α}, Iff (LT.lt.{u1} α _inst_2 (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) a) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)))))))) (LT.lt.{u1} α _inst_2 (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))))) a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LT.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.1388 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.1390 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.1388 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.1390) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.1403 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.1405 : α) => LT.lt.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.1403 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.1405)] {a : α}, Iff (LT.lt.{u1} α _inst_2 (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1)))) a) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (InvOneClass.toOne.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1))))))) (LT.lt.{u1} α _inst_2 (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (InvOneClass.toOne.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1)))))) a)
Case conversion may be inaccurate. Consider using '#align inv_lt_one' inv_lt_one'ₓ'. -/
alias Left.inv_lt_one_iff ← inv_lt_one'
#align inv_lt_one' inv_lt_one'

attribute [to_additive neg_lt_zero] inv_lt_one'

/- warning: inv_of_one_lt_inv -> inv_of_one_lt_inv is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LT.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)))))) (LT.lt.{u1} α _inst_2)] {a : α}, (LT.lt.{u1} α _inst_2 (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))))) (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) a)) -> (LT.lt.{u1} α _inst_2 a (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LT.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.1291 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.1293 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.1291 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.1293) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.1306 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.1308 : α) => LT.lt.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.1306 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.1308)] {a : α}, (LT.lt.{u1} α _inst_2 (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (InvOneClass.toOne.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1)))))) (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1)))) a)) -> (LT.lt.{u1} α _inst_2 a (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (InvOneClass.toOne.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1)))))))
Case conversion may be inaccurate. Consider using '#align inv_of_one_lt_inv inv_of_one_lt_invₓ'. -/
alias Left.one_lt_inv_iff ↔ inv_of_one_lt_inv _
#align inv_of_one_lt_inv inv_of_one_lt_inv

attribute [to_additive neg_of_neg_pos] inv_of_one_lt_inv

/- warning: one_lt_inv_of_inv -> one_lt_inv_of_inv is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LT.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)))))) (LT.lt.{u1} α _inst_2)] {a : α}, (LT.lt.{u1} α _inst_2 a (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)))))))) -> (LT.lt.{u1} α _inst_2 (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))))) (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) a))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LT.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.1291 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.1293 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.1291 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.1293) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.1306 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.1308 : α) => LT.lt.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.1306 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.1308)] {a : α}, (LT.lt.{u1} α _inst_2 a (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (InvOneClass.toOne.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1))))))) -> (LT.lt.{u1} α _inst_2 (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (InvOneClass.toOne.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1)))))) (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1)))) a))
Case conversion may be inaccurate. Consider using '#align one_lt_inv_of_inv one_lt_inv_of_invₓ'. -/
alias Left.one_lt_inv_iff ↔ _ one_lt_inv_of_inv
#align one_lt_inv_of_inv one_lt_inv_of_inv

attribute [to_additive neg_pos_of_neg] one_lt_inv_of_inv

/- warning: mul_le_of_le_inv_mul -> mul_le_of_le_inv_mul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LE.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)))))) (LE.le.{u1} α _inst_2)] {a : α} {b : α} {c : α}, (LE.le.{u1} α _inst_2 b (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) a) c)) -> (LE.le.{u1} α _inst_2 (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) a b) c)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LE.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.645 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.647 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.645 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.647) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.660 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.662 : α) => LE.le.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.660 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.662)] {a : α} {b : α} {c : α}, (LE.le.{u1} α _inst_2 b (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1)))) a) c)) -> (LE.le.{u1} α _inst_2 (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) a b) c)
Case conversion may be inaccurate. Consider using '#align mul_le_of_le_inv_mul mul_le_of_le_inv_mulₓ'. -/
alias le_inv_mul_iff_mul_le ↔ mul_le_of_le_inv_mul _
#align mul_le_of_le_inv_mul mul_le_of_le_inv_mul

attribute [to_additive] mul_le_of_le_inv_mul

/- warning: le_inv_mul_of_mul_le -> le_inv_mul_of_mul_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LE.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)))))) (LE.le.{u1} α _inst_2)] {a : α} {b : α} {c : α}, (LE.le.{u1} α _inst_2 (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) a b) c) -> (LE.le.{u1} α _inst_2 b (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) a) c))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LE.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.645 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.647 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.645 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.647) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.660 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.662 : α) => LE.le.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.660 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.662)] {a : α} {b : α} {c : α}, (LE.le.{u1} α _inst_2 (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) a b) c) -> (LE.le.{u1} α _inst_2 b (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1)))) a) c))
Case conversion may be inaccurate. Consider using '#align le_inv_mul_of_mul_le le_inv_mul_of_mul_leₓ'. -/
alias le_inv_mul_iff_mul_le ↔ _ le_inv_mul_of_mul_le
#align le_inv_mul_of_mul_le le_inv_mul_of_mul_le

attribute [to_additive] le_inv_mul_of_mul_le

/- warning: inv_mul_le_of_le_mul -> inv_mul_le_of_le_mul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LE.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)))))) (LE.le.{u1} α _inst_2)] {a : α} {b : α} {c : α}, (LE.le.{u1} α _inst_2 a (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) b c)) -> (LE.le.{u1} α _inst_2 (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) b) a) c)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LE.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.746 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.748 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.746 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.748) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.761 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.763 : α) => LE.le.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.761 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.763)] {a : α} {b : α} {c : α}, (LE.le.{u1} α _inst_2 a (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) b c)) -> (LE.le.{u1} α _inst_2 (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1)))) b) a) c)
Case conversion may be inaccurate. Consider using '#align inv_mul_le_of_le_mul inv_mul_le_of_le_mulₓ'. -/
alias inv_mul_le_iff_le_mul ↔ _ inv_mul_le_of_le_mul
#align inv_mul_le_of_le_mul inv_mul_le_of_le_mul

attribute [to_additive] inv_mul_le_iff_le_mul

/- warning: mul_lt_of_lt_inv_mul -> mul_lt_of_lt_inv_mul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LT.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)))))) (LT.lt.{u1} α _inst_2)] {a : α} {b : α} {c : α}, (LT.lt.{u1} α _inst_2 b (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) a) c)) -> (LT.lt.{u1} α _inst_2 (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) a b) c)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LT.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.1482 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.1484 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.1482 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.1484) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.1497 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.1499 : α) => LT.lt.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.1497 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.1499)] {a : α} {b : α} {c : α}, (LT.lt.{u1} α _inst_2 b (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1)))) a) c)) -> (LT.lt.{u1} α _inst_2 (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) a b) c)
Case conversion may be inaccurate. Consider using '#align mul_lt_of_lt_inv_mul mul_lt_of_lt_inv_mulₓ'. -/
alias lt_inv_mul_iff_mul_lt ↔ mul_lt_of_lt_inv_mul _
#align mul_lt_of_lt_inv_mul mul_lt_of_lt_inv_mul

attribute [to_additive] mul_lt_of_lt_inv_mul

/- warning: lt_inv_mul_of_mul_lt -> lt_inv_mul_of_mul_lt is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LT.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)))))) (LT.lt.{u1} α _inst_2)] {a : α} {b : α} {c : α}, (LT.lt.{u1} α _inst_2 (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) a b) c) -> (LT.lt.{u1} α _inst_2 b (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) a) c))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LT.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.1482 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.1484 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.1482 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.1484) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.1497 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.1499 : α) => LT.lt.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.1497 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.1499)] {a : α} {b : α} {c : α}, (LT.lt.{u1} α _inst_2 (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) a b) c) -> (LT.lt.{u1} α _inst_2 b (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1)))) a) c))
Case conversion may be inaccurate. Consider using '#align lt_inv_mul_of_mul_lt lt_inv_mul_of_mul_ltₓ'. -/
alias lt_inv_mul_iff_mul_lt ↔ _ lt_inv_mul_of_mul_lt
#align lt_inv_mul_of_mul_lt lt_inv_mul_of_mul_lt

attribute [to_additive] lt_inv_mul_of_mul_lt

/- warning: lt_mul_of_inv_mul_lt -> lt_mul_of_inv_mul_lt is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LT.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)))))) (LT.lt.{u1} α _inst_2)] {a : α} {b : α} {c : α}, (LT.lt.{u1} α _inst_2 (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) b) a) c) -> (LT.lt.{u1} α _inst_2 a (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) b c))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LT.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.1582 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.1584 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.1582 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.1584) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.1597 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.1599 : α) => LT.lt.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.1597 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.1599)] {a : α} {b : α} {c : α}, (LT.lt.{u1} α _inst_2 (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1)))) b) a) c) -> (LT.lt.{u1} α _inst_2 a (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) b c))
Case conversion may be inaccurate. Consider using '#align lt_mul_of_inv_mul_lt lt_mul_of_inv_mul_ltₓ'. -/
/- warning: inv_mul_lt_of_lt_mul -> inv_mul_lt_of_lt_mul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LT.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)))))) (LT.lt.{u1} α _inst_2)] {a : α} {b : α} {c : α}, (LT.lt.{u1} α _inst_2 a (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) b c)) -> (LT.lt.{u1} α _inst_2 (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) b) a) c)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LT.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.1582 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.1584 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.1582 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.1584) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.1597 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.1599 : α) => LT.lt.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.1597 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.1599)] {a : α} {b : α} {c : α}, (LT.lt.{u1} α _inst_2 a (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) b c)) -> (LT.lt.{u1} α _inst_2 (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1)))) b) a) c)
Case conversion may be inaccurate. Consider using '#align inv_mul_lt_of_lt_mul inv_mul_lt_of_lt_mulₓ'. -/
alias inv_mul_lt_iff_lt_mul ↔ lt_mul_of_inv_mul_lt inv_mul_lt_of_lt_mul
#align lt_mul_of_inv_mul_lt lt_mul_of_inv_mul_lt
#align inv_mul_lt_of_lt_mul inv_mul_lt_of_lt_mul

attribute [to_additive] lt_mul_of_inv_mul_lt

attribute [to_additive] inv_mul_lt_of_lt_mul

/- warning: lt_mul_of_inv_mul_lt_left -> lt_mul_of_inv_mul_lt_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LT.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)))))) (LT.lt.{u1} α _inst_2)] {a : α} {b : α} {c : α}, (LT.lt.{u1} α _inst_2 (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) b) a) c) -> (LT.lt.{u1} α _inst_2 a (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) b c))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LT.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.1582 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.1584 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.1582 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.1584) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.1597 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.1599 : α) => LT.lt.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.1597 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.1599)] {a : α} {b : α} {c : α}, (LT.lt.{u1} α _inst_2 (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1)))) b) a) c) -> (LT.lt.{u1} α _inst_2 a (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) b c))
Case conversion may be inaccurate. Consider using '#align lt_mul_of_inv_mul_lt_left lt_mul_of_inv_mul_lt_leftₓ'. -/
alias lt_mul_of_inv_mul_lt ← lt_mul_of_inv_mul_lt_left
#align lt_mul_of_inv_mul_lt_left lt_mul_of_inv_mul_lt_left

attribute [to_additive] lt_mul_of_inv_mul_lt_left

/- warning: inv_le_one' -> inv_le_one' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LE.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)))))) (LE.le.{u1} α _inst_2)] {a : α}, Iff (LE.le.{u1} α _inst_2 (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) a) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)))))))) (LE.le.{u1} α _inst_2 (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))))) a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LE.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.446 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.448 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.446 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.448) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.461 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.463 : α) => LE.le.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.461 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.463)] {a : α}, Iff (LE.le.{u1} α _inst_2 (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1)))) a) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (InvOneClass.toOne.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1))))))) (LE.le.{u1} α _inst_2 (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (InvOneClass.toOne.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1)))))) a)
Case conversion may be inaccurate. Consider using '#align inv_le_one' inv_le_one'ₓ'. -/
alias Left.inv_le_one_iff ← inv_le_one'
#align inv_le_one' inv_le_one'

attribute [to_additive neg_nonpos] inv_le_one'

/- warning: one_le_inv' -> one_le_inv' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LE.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)))))) (LE.le.{u1} α _inst_2)] {a : α}, Iff (LE.le.{u1} α _inst_2 (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))))) (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) a)) (LE.le.{u1} α _inst_2 a (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LE.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.547 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.549 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.547 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.549) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.562 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.564 : α) => LE.le.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.562 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.564)] {a : α}, Iff (LE.le.{u1} α _inst_2 (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (InvOneClass.toOne.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1)))))) (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1)))) a)) (LE.le.{u1} α _inst_2 a (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (InvOneClass.toOne.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1)))))))
Case conversion may be inaccurate. Consider using '#align one_le_inv' one_le_inv'ₓ'. -/
alias Left.one_le_inv_iff ← one_le_inv'
#align one_le_inv' one_le_inv'

attribute [to_additive neg_nonneg] one_le_inv'

/- warning: one_lt_inv' -> one_lt_inv' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LT.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)))))) (LT.lt.{u1} α _inst_2)] {a : α}, Iff (LT.lt.{u1} α _inst_2 (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))))) (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) a)) (LT.lt.{u1} α _inst_2 a (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LT.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.1291 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.1293 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.1291 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.1293) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.1306 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.1308 : α) => LT.lt.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.1306 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.1308)] {a : α}, Iff (LT.lt.{u1} α _inst_2 (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (InvOneClass.toOne.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1)))))) (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1)))) a)) (LT.lt.{u1} α _inst_2 a (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (InvOneClass.toOne.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1)))))))
Case conversion may be inaccurate. Consider using '#align one_lt_inv' one_lt_inv'ₓ'. -/
alias Left.one_lt_inv_iff ← one_lt_inv'
#align one_lt_inv' one_lt_inv'

attribute [to_additive neg_pos] one_lt_inv'

alias mul_lt_mul_left' ← OrderedCommGroup.mul_lt_mul_left'
#align ordered_comm_group.mul_lt_mul_left' OrderedCommGroup.mul_lt_mul_left'

attribute [to_additive OrderedAddCommGroup.add_lt_add_left] OrderedCommGroup.mul_lt_mul_left'

alias le_of_mul_le_mul_left' ← OrderedCommGroup.le_of_mul_le_mul_left
#align ordered_comm_group.le_of_mul_le_mul_left OrderedCommGroup.le_of_mul_le_mul_left

attribute [to_additive OrderedAddCommGroup.le_of_add_le_add_left]
  OrderedCommGroup.le_of_mul_le_mul_left

alias lt_of_mul_lt_mul_left' ← OrderedCommGroup.lt_of_mul_lt_mul_left
#align ordered_comm_group.lt_of_mul_lt_mul_left OrderedCommGroup.lt_of_mul_lt_mul_left

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
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LE.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.6956 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.6958 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.6956 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.6958)) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.6971 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.6973 : α) => LE.le.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.6971 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.6973)] {a : α} {b : α} (c : α), Iff (LE.le.{u1} α _inst_2 (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toDiv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))) a c) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toDiv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))) b c)) (LE.le.{u1} α _inst_2 a b)
Case conversion may be inaccurate. Consider using '#align div_le_div_iff_right div_le_div_iff_rightₓ'. -/
@[simp, to_additive]
theorem div_le_div_iff_right (c : α) : a / c ≤ b / c ↔ a ≤ b := by
  simpa only [div_eq_mul_inv] using mul_le_mul_iff_right _
#align div_le_div_iff_right div_le_div_iff_right
#align sub_le_sub_iff_right sub_le_sub_iff_right

/- warning: div_le_div_right' -> div_le_div_right' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LE.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))))) (LE.le.{u1} α _inst_2)] {a : α} {b : α}, (LE.le.{u1} α _inst_2 a b) -> (forall (c : α), LE.le.{u1} α _inst_2 (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toHasDiv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))) a c) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toHasDiv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))) b c))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LE.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.7034 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.7036 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.7034 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.7036)) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.7049 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.7051 : α) => LE.le.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.7049 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.7051)] {a : α} {b : α}, (LE.le.{u1} α _inst_2 a b) -> (forall (c : α), LE.le.{u1} α _inst_2 (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toDiv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))) a c) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toDiv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))) b c))
Case conversion may be inaccurate. Consider using '#align div_le_div_right' div_le_div_right'ₓ'. -/
@[to_additive sub_le_sub_right]
theorem div_le_div_right' (h : a ≤ b) (c : α) : a / c ≤ b / c :=
  (div_le_div_iff_right c).2 h
#align div_le_div_right' div_le_div_right'
#align sub_le_sub_right sub_le_sub_right

/- warning: one_le_div' -> one_le_div' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LE.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))))) (LE.le.{u1} α _inst_2)] {a : α} {b : α}, Iff (LE.le.{u1} α _inst_2 (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))))) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toHasDiv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))) a b)) (LE.le.{u1} α _inst_2 b a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LE.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.7106 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.7108 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.7106 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.7108)) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.7121 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.7123 : α) => LE.le.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.7121 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.7123)] {a : α} {b : α}, Iff (LE.le.{u1} α _inst_2 (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (InvOneClass.toOne.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1)))))) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toDiv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))) a b)) (LE.le.{u1} α _inst_2 b a)
Case conversion may be inaccurate. Consider using '#align one_le_div' one_le_div'ₓ'. -/
@[simp, to_additive sub_nonneg]
theorem one_le_div' : 1 ≤ a / b ↔ b ≤ a := by
  rw [← mul_le_mul_iff_right b, one_mul, div_eq_mul_inv, inv_mul_cancel_right]
#align one_le_div' one_le_div'
#align sub_nonneg sub_nonneg

/- warning: le_of_sub_nonneg -> le_of_sub_nonneg is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : AddGroup.{u1} α] [_inst_2 : LE.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α _inst_1))))))) (LE.le.{u1} α _inst_2)] {a : α} {b : α}, (LE.le.{u1} α _inst_2 (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α _inst_1))))))) (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α (SubNegMonoid.toHasSub.{u1} α (AddGroup.toSubNegMonoid.{u1} α _inst_1))) a b)) -> (LE.le.{u1} α _inst_2 b a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : AddGroup.{u1} α] [_inst_2 : LE.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.7106 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.7108 : α) => HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α _inst_1))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.7106 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.7108)) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.7121 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.7123 : α) => LE.le.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.7121 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.7123)] {a : α} {b : α}, (LE.le.{u1} α _inst_2 (OfNat.ofNat.{u1} α 0 (Zero.toOfNat0.{u1} α (NegZeroClass.toZero.{u1} α (SubNegZeroMonoid.toNegZeroClass.{u1} α (SubtractionMonoid.toSubNegZeroMonoid.{u1} α (AddGroup.toSubtractionMonoid.{u1} α _inst_1)))))) (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α (SubNegMonoid.toSub.{u1} α (AddGroup.toSubNegMonoid.{u1} α _inst_1))) a b)) -> (LE.le.{u1} α _inst_2 b a)
Case conversion may be inaccurate. Consider using '#align le_of_sub_nonneg le_of_sub_nonnegₓ'. -/
/- warning: sub_nonneg_of_le -> sub_nonneg_of_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : AddGroup.{u1} α] [_inst_2 : LE.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α _inst_1))))))) (LE.le.{u1} α _inst_2)] {a : α} {b : α}, (LE.le.{u1} α _inst_2 b a) -> (LE.le.{u1} α _inst_2 (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α _inst_1))))))) (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α (SubNegMonoid.toHasSub.{u1} α (AddGroup.toSubNegMonoid.{u1} α _inst_1))) a b))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : AddGroup.{u1} α] [_inst_2 : LE.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.7106 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.7108 : α) => HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α _inst_1))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.7106 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.7108)) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.7121 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.7123 : α) => LE.le.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.7121 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.7123)] {a : α} {b : α}, (LE.le.{u1} α _inst_2 b a) -> (LE.le.{u1} α _inst_2 (OfNat.ofNat.{u1} α 0 (Zero.toOfNat0.{u1} α (NegZeroClass.toZero.{u1} α (SubNegZeroMonoid.toNegZeroClass.{u1} α (SubtractionMonoid.toSubNegZeroMonoid.{u1} α (AddGroup.toSubtractionMonoid.{u1} α _inst_1)))))) (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α (SubNegMonoid.toSub.{u1} α (AddGroup.toSubNegMonoid.{u1} α _inst_1))) a b))
Case conversion may be inaccurate. Consider using '#align sub_nonneg_of_le sub_nonneg_of_leₓ'. -/
alias sub_nonneg ↔ le_of_sub_nonneg sub_nonneg_of_le
#align le_of_sub_nonneg le_of_sub_nonneg
#align sub_nonneg_of_le sub_nonneg_of_le

/- warning: div_le_one' -> div_le_one' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LE.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))))) (LE.le.{u1} α _inst_2)] {a : α} {b : α}, Iff (LE.le.{u1} α _inst_2 (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toHasDiv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))) a b) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)))))))) (LE.le.{u1} α _inst_2 a b)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LE.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.7207 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.7209 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.7207 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.7209)) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.7222 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.7224 : α) => LE.le.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.7222 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.7224)] {a : α} {b : α}, Iff (LE.le.{u1} α _inst_2 (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toDiv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))) a b) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (InvOneClass.toOne.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1))))))) (LE.le.{u1} α _inst_2 a b)
Case conversion may be inaccurate. Consider using '#align div_le_one' div_le_one'ₓ'. -/
@[simp, to_additive sub_nonpos]
theorem div_le_one' : a / b ≤ 1 ↔ a ≤ b := by
  rw [← mul_le_mul_iff_right b, one_mul, div_eq_mul_inv, inv_mul_cancel_right]
#align div_le_one' div_le_one'
#align sub_nonpos sub_nonpos

/- warning: le_of_sub_nonpos -> le_of_sub_nonpos is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : AddGroup.{u1} α] [_inst_2 : LE.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α _inst_1))))))) (LE.le.{u1} α _inst_2)] {a : α} {b : α}, (LE.le.{u1} α _inst_2 (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α (SubNegMonoid.toHasSub.{u1} α (AddGroup.toSubNegMonoid.{u1} α _inst_1))) a b) (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α _inst_1)))))))) -> (LE.le.{u1} α _inst_2 a b)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : AddGroup.{u1} α] [_inst_2 : LE.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.7207 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.7209 : α) => HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α _inst_1))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.7207 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.7209)) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.7222 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.7224 : α) => LE.le.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.7222 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.7224)] {a : α} {b : α}, (LE.le.{u1} α _inst_2 (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α (SubNegMonoid.toSub.{u1} α (AddGroup.toSubNegMonoid.{u1} α _inst_1))) a b) (OfNat.ofNat.{u1} α 0 (Zero.toOfNat0.{u1} α (NegZeroClass.toZero.{u1} α (SubNegZeroMonoid.toNegZeroClass.{u1} α (SubtractionMonoid.toSubNegZeroMonoid.{u1} α (AddGroup.toSubtractionMonoid.{u1} α _inst_1))))))) -> (LE.le.{u1} α _inst_2 a b)
Case conversion may be inaccurate. Consider using '#align le_of_sub_nonpos le_of_sub_nonposₓ'. -/
/- warning: sub_nonpos_of_le -> sub_nonpos_of_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : AddGroup.{u1} α] [_inst_2 : LE.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α _inst_1))))))) (LE.le.{u1} α _inst_2)] {a : α} {b : α}, (LE.le.{u1} α _inst_2 a b) -> (LE.le.{u1} α _inst_2 (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α (SubNegMonoid.toHasSub.{u1} α (AddGroup.toSubNegMonoid.{u1} α _inst_1))) a b) (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α _inst_1))))))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : AddGroup.{u1} α] [_inst_2 : LE.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.7207 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.7209 : α) => HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α _inst_1))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.7207 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.7209)) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.7222 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.7224 : α) => LE.le.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.7222 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.7224)] {a : α} {b : α}, (LE.le.{u1} α _inst_2 a b) -> (LE.le.{u1} α _inst_2 (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α (SubNegMonoid.toSub.{u1} α (AddGroup.toSubNegMonoid.{u1} α _inst_1))) a b) (OfNat.ofNat.{u1} α 0 (Zero.toOfNat0.{u1} α (NegZeroClass.toZero.{u1} α (SubNegZeroMonoid.toNegZeroClass.{u1} α (SubtractionMonoid.toSubNegZeroMonoid.{u1} α (AddGroup.toSubtractionMonoid.{u1} α _inst_1)))))))
Case conversion may be inaccurate. Consider using '#align sub_nonpos_of_le sub_nonpos_of_leₓ'. -/
alias sub_nonpos ↔ le_of_sub_nonpos sub_nonpos_of_le
#align le_of_sub_nonpos le_of_sub_nonpos
#align sub_nonpos_of_le sub_nonpos_of_le

/- warning: le_div_iff_mul_le -> le_div_iff_mul_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LE.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))))) (LE.le.{u1} α _inst_2)] {a : α} {b : α} {c : α}, Iff (LE.le.{u1} α _inst_2 a (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toHasDiv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))) c b)) (LE.le.{u1} α _inst_2 (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) a b) c)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LE.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.7308 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.7310 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.7308 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.7310)) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.7323 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.7325 : α) => LE.le.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.7323 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.7325)] {a : α} {b : α} {c : α}, Iff (LE.le.{u1} α _inst_2 a (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toDiv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))) c b)) (LE.le.{u1} α _inst_2 (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) a b) c)
Case conversion may be inaccurate. Consider using '#align le_div_iff_mul_le le_div_iff_mul_leₓ'. -/
@[to_additive]
theorem le_div_iff_mul_le : a ≤ c / b ↔ a * b ≤ c := by
  rw [← mul_le_mul_iff_right b, div_eq_mul_inv, inv_mul_cancel_right]
#align le_div_iff_mul_le le_div_iff_mul_le
#align le_sub_iff_add_le le_sub_iff_add_le

/- warning: add_le_of_le_sub_right -> add_le_of_le_sub_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : AddGroup.{u1} α] [_inst_2 : LE.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α _inst_1))))))) (LE.le.{u1} α _inst_2)] {a : α} {b : α} {c : α}, (LE.le.{u1} α _inst_2 a (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α (SubNegMonoid.toHasSub.{u1} α (AddGroup.toSubNegMonoid.{u1} α _inst_1))) c b)) -> (LE.le.{u1} α _inst_2 (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α _inst_1))))) a b) c)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : AddGroup.{u1} α] [_inst_2 : LE.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.7308 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.7310 : α) => HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α _inst_1))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.7308 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.7310)) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.7323 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.7325 : α) => LE.le.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.7323 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.7325)] {a : α} {b : α} {c : α}, (LE.le.{u1} α _inst_2 a (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α (SubNegMonoid.toSub.{u1} α (AddGroup.toSubNegMonoid.{u1} α _inst_1))) c b)) -> (LE.le.{u1} α _inst_2 (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α _inst_1))))) a b) c)
Case conversion may be inaccurate. Consider using '#align add_le_of_le_sub_right add_le_of_le_sub_rightₓ'. -/
/- warning: le_sub_right_of_add_le -> le_sub_right_of_add_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : AddGroup.{u1} α] [_inst_2 : LE.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α _inst_1))))))) (LE.le.{u1} α _inst_2)] {a : α} {b : α} {c : α}, (LE.le.{u1} α _inst_2 (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α _inst_1))))) a b) c) -> (LE.le.{u1} α _inst_2 a (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α (SubNegMonoid.toHasSub.{u1} α (AddGroup.toSubNegMonoid.{u1} α _inst_1))) c b))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : AddGroup.{u1} α] [_inst_2 : LE.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.7308 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.7310 : α) => HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α _inst_1))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.7308 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.7310)) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.7323 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.7325 : α) => LE.le.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.7323 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.7325)] {a : α} {b : α} {c : α}, (LE.le.{u1} α _inst_2 (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α _inst_1))))) a b) c) -> (LE.le.{u1} α _inst_2 a (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α (SubNegMonoid.toSub.{u1} α (AddGroup.toSubNegMonoid.{u1} α _inst_1))) c b))
Case conversion may be inaccurate. Consider using '#align le_sub_right_of_add_le le_sub_right_of_add_leₓ'. -/
alias le_sub_iff_add_le ↔ add_le_of_le_sub_right le_sub_right_of_add_le
#align add_le_of_le_sub_right add_le_of_le_sub_right
#align le_sub_right_of_add_le le_sub_right_of_add_le

/- warning: div_le_iff_le_mul -> div_le_iff_le_mul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LE.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))))) (LE.le.{u1} α _inst_2)] {a : α} {b : α} {c : α}, Iff (LE.le.{u1} α _inst_2 (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toHasDiv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))) a c) b) (LE.le.{u1} α _inst_2 a (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) b c))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LE.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.7410 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.7412 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.7410 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.7412)) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.7425 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.7427 : α) => LE.le.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.7425 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.7427)] {a : α} {b : α} {c : α}, Iff (LE.le.{u1} α _inst_2 (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toDiv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))) a c) b) (LE.le.{u1} α _inst_2 a (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) b c))
Case conversion may be inaccurate. Consider using '#align div_le_iff_le_mul div_le_iff_le_mulₓ'. -/
@[to_additive]
theorem div_le_iff_le_mul : a / c ≤ b ↔ a ≤ b * c := by
  rw [← mul_le_mul_iff_right c, div_eq_mul_inv, inv_mul_cancel_right]
#align div_le_iff_le_mul div_le_iff_le_mul
#align sub_le_iff_le_add sub_le_iff_le_add

/- warning: add_group.to_has_ordered_sub -> AddGroup.toHasOrderedSub is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_4 : AddGroup.{u1} α] [_inst_5 : LE.{u1} α] [_inst_6 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α _inst_4))))))) (LE.le.{u1} α _inst_5)], OrderedSub.{u1} α _inst_5 (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α _inst_4)))) (SubNegMonoid.toHasSub.{u1} α (AddGroup.toSubNegMonoid.{u1} α _inst_4))
but is expected to have type
  forall {α : Type.{u1}} [_inst_4 : AddGroup.{u1} α] [_inst_5 : LE.{u1} α] [_inst_6 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.7560 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.7562 : α) => HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α _inst_4))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.7560 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.7562)) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.7575 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.7577 : α) => LE.le.{u1} α _inst_5 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.7575 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.7577)], OrderedSub.{u1} α _inst_5 (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α _inst_4)))) (SubNegMonoid.toSub.{u1} α (AddGroup.toSubNegMonoid.{u1} α _inst_4))
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
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LE.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.7748 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.7750 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.7748 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.7750) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.7763 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.7765 : α) => LE.le.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.7763 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.7765)] [_inst_4 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.7785 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.7787 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.7785 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.7787)) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.7800 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.7802 : α) => LE.le.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.7800 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.7802)] {b : α} {c : α} (a : α), Iff (LE.le.{u1} α _inst_2 (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toDiv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))) a b) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toDiv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))) a c)) (LE.le.{u1} α _inst_2 c b)
Case conversion may be inaccurate. Consider using '#align div_le_div_iff_left div_le_div_iff_leftₓ'. -/
@[simp, to_additive]
theorem div_le_div_iff_left (a : α) : a / b ≤ a / c ↔ c ≤ b := by
  rw [div_eq_mul_inv, div_eq_mul_inv, ← mul_le_mul_iff_left a⁻¹, inv_mul_cancel_left,
    inv_mul_cancel_left, inv_le_inv_iff]
#align div_le_div_iff_left div_le_div_iff_left
#align sub_le_sub_iff_left sub_le_sub_iff_left

/- warning: div_le_div_left' -> div_le_div_left' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LE.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)))))) (LE.le.{u1} α _inst_2)] [_inst_4 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))))) (LE.le.{u1} α _inst_2)] {a : α} {b : α}, (LE.le.{u1} α _inst_2 a b) -> (forall (c : α), LE.le.{u1} α _inst_2 (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toHasDiv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))) c b) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toHasDiv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))) c a))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LE.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.7887 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.7889 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.7887 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.7889) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.7902 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.7904 : α) => LE.le.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.7902 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.7904)] [_inst_4 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.7924 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.7926 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.7924 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.7926)) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.7939 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.7941 : α) => LE.le.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.7939 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.7941)] {a : α} {b : α}, (LE.le.{u1} α _inst_2 a b) -> (forall (c : α), LE.le.{u1} α _inst_2 (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toDiv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))) c b) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toDiv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))) c a))
Case conversion may be inaccurate. Consider using '#align div_le_div_left' div_le_div_left'ₓ'. -/
@[to_additive sub_le_sub_left]
theorem div_le_div_left' (h : a ≤ b) (c : α) : c / b ≤ c / a :=
  (div_le_div_iff_left c).2 h
#align div_le_div_left' div_le_div_left'
#align sub_le_sub_left sub_le_sub_left

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
#align sub_le_sub_iff sub_le_sub_iff

/- warning: le_div_iff_mul_le' -> le_div_iff_mul_le' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CommGroup.{u1} α] [_inst_2 : LE.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1))))))) (LE.le.{u1} α _inst_2)] {a : α} {b : α} {c : α}, Iff (LE.le.{u1} α _inst_2 b (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toHasDiv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1)))) c a)) (LE.le.{u1} α _inst_2 (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1)))))) a b) c)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CommGroup.{u1} α] [_inst_2 : LE.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.8131 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.8133 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1)))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.8131 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.8133) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.8146 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.8148 : α) => LE.le.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.8146 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.8148)] {a : α} {b : α} {c : α}, Iff (LE.le.{u1} α _inst_2 b (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toDiv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1)))) c a)) (LE.le.{u1} α _inst_2 (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1)))))) a b) c)
Case conversion may be inaccurate. Consider using '#align le_div_iff_mul_le' le_div_iff_mul_le'ₓ'. -/
@[to_additive]
theorem le_div_iff_mul_le' : b ≤ c / a ↔ a * b ≤ c := by rw [le_div_iff_mul_le, mul_comm]
#align le_div_iff_mul_le' le_div_iff_mul_le'
#align le_sub_iff_add_le' le_sub_iff_add_le'

/- warning: add_le_of_le_sub_left -> add_le_of_le_sub_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : AddCommGroup.{u1} α] [_inst_2 : LE.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_1))))))) (LE.le.{u1} α _inst_2)] {a : α} {b : α} {c : α}, (LE.le.{u1} α _inst_2 b (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α (SubNegMonoid.toHasSub.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_1)))) c a)) -> (LE.le.{u1} α _inst_2 (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_1)))))) a b) c)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : AddCommGroup.{u1} α] [_inst_2 : LE.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.8131 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.8133 : α) => HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_1)))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.8131 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.8133) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.8146 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.8148 : α) => LE.le.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.8146 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.8148)] {a : α} {b : α} {c : α}, (LE.le.{u1} α _inst_2 b (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α (SubNegMonoid.toSub.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_1)))) c a)) -> (LE.le.{u1} α _inst_2 (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_1)))))) a b) c)
Case conversion may be inaccurate. Consider using '#align add_le_of_le_sub_left add_le_of_le_sub_leftₓ'. -/
/- warning: le_sub_left_of_add_le -> le_sub_left_of_add_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : AddCommGroup.{u1} α] [_inst_2 : LE.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_1))))))) (LE.le.{u1} α _inst_2)] {a : α} {b : α} {c : α}, (LE.le.{u1} α _inst_2 (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_1)))))) a b) c) -> (LE.le.{u1} α _inst_2 b (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α (SubNegMonoid.toHasSub.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_1)))) c a))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : AddCommGroup.{u1} α] [_inst_2 : LE.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.8131 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.8133 : α) => HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_1)))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.8131 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.8133) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.8146 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.8148 : α) => LE.le.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.8146 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.8148)] {a : α} {b : α} {c : α}, (LE.le.{u1} α _inst_2 (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_1)))))) a b) c) -> (LE.le.{u1} α _inst_2 b (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α (SubNegMonoid.toSub.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_1)))) c a))
Case conversion may be inaccurate. Consider using '#align le_sub_left_of_add_le le_sub_left_of_add_leₓ'. -/
alias le_sub_iff_add_le' ↔ add_le_of_le_sub_left le_sub_left_of_add_le
#align add_le_of_le_sub_left add_le_of_le_sub_left
#align le_sub_left_of_add_le le_sub_left_of_add_le

/- warning: div_le_iff_le_mul' -> div_le_iff_le_mul' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CommGroup.{u1} α] [_inst_2 : LE.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1))))))) (LE.le.{u1} α _inst_2)] {a : α} {b : α} {c : α}, Iff (LE.le.{u1} α _inst_2 (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toHasDiv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1)))) a b) c) (LE.le.{u1} α _inst_2 a (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1)))))) b c))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CommGroup.{u1} α] [_inst_2 : LE.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.8228 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.8230 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1)))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.8228 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.8230) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.8243 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.8245 : α) => LE.le.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.8243 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.8245)] {a : α} {b : α} {c : α}, Iff (LE.le.{u1} α _inst_2 (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toDiv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1)))) a b) c) (LE.le.{u1} α _inst_2 a (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1)))))) b c))
Case conversion may be inaccurate. Consider using '#align div_le_iff_le_mul' div_le_iff_le_mul'ₓ'. -/
@[to_additive]
theorem div_le_iff_le_mul' : a / b ≤ c ↔ a ≤ b * c := by rw [div_le_iff_le_mul, mul_comm]
#align div_le_iff_le_mul' div_le_iff_le_mul'
#align sub_le_iff_le_add' sub_le_iff_le_add'

/- warning: le_add_of_sub_left_le -> le_add_of_sub_left_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : AddCommGroup.{u1} α] [_inst_2 : LE.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_1))))))) (LE.le.{u1} α _inst_2)] {a : α} {b : α} {c : α}, (LE.le.{u1} α _inst_2 (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α (SubNegMonoid.toHasSub.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_1)))) a b) c) -> (LE.le.{u1} α _inst_2 a (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_1)))))) b c))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : AddCommGroup.{u1} α] [_inst_2 : LE.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.8228 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.8230 : α) => HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_1)))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.8228 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.8230) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.8243 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.8245 : α) => LE.le.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.8243 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.8245)] {a : α} {b : α} {c : α}, (LE.le.{u1} α _inst_2 (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α (SubNegMonoid.toSub.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_1)))) a b) c) -> (LE.le.{u1} α _inst_2 a (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_1)))))) b c))
Case conversion may be inaccurate. Consider using '#align le_add_of_sub_left_le le_add_of_sub_left_leₓ'. -/
/- warning: sub_left_le_of_le_add -> sub_left_le_of_le_add is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : AddCommGroup.{u1} α] [_inst_2 : LE.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_1))))))) (LE.le.{u1} α _inst_2)] {a : α} {b : α} {c : α}, (LE.le.{u1} α _inst_2 a (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_1)))))) b c)) -> (LE.le.{u1} α _inst_2 (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α (SubNegMonoid.toHasSub.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_1)))) a b) c)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : AddCommGroup.{u1} α] [_inst_2 : LE.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.8228 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.8230 : α) => HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_1)))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.8228 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.8230) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.8243 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.8245 : α) => LE.le.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.8243 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.8245)] {a : α} {b : α} {c : α}, (LE.le.{u1} α _inst_2 a (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_1)))))) b c)) -> (LE.le.{u1} α _inst_2 (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α (SubNegMonoid.toSub.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_1)))) a b) c)
Case conversion may be inaccurate. Consider using '#align sub_left_le_of_le_add sub_left_le_of_le_addₓ'. -/
alias sub_le_iff_le_add' ↔ le_add_of_sub_left_le sub_left_le_of_le_add
#align le_add_of_sub_left_le le_add_of_sub_left_le
#align sub_left_le_of_le_add sub_left_le_of_le_add

/- warning: inv_le_div_iff_le_mul -> inv_le_div_iff_le_mul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CommGroup.{u1} α] [_inst_2 : LE.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1))))))) (LE.le.{u1} α _inst_2)] {a : α} {b : α} {c : α}, Iff (LE.le.{u1} α _inst_2 (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1))) b) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toHasDiv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1)))) a c)) (LE.le.{u1} α _inst_2 c (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1)))))) a b))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CommGroup.{u1} α] [_inst_2 : LE.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.8325 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.8327 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1)))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.8325 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.8327) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.8340 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.8342 : α) => LE.le.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.8340 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.8342)] {a : α} {b : α} {c : α}, Iff (LE.le.{u1} α _inst_2 (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α (CommGroup.toDivisionCommMonoid.{u1} α _inst_1))))) b) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toDiv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1)))) a c)) (LE.le.{u1} α _inst_2 c (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1)))))) a b))
Case conversion may be inaccurate. Consider using '#align inv_le_div_iff_le_mul inv_le_div_iff_le_mulₓ'. -/
@[simp, to_additive]
theorem inv_le_div_iff_le_mul : b⁻¹ ≤ a / c ↔ c ≤ a * b :=
  le_div_iff_mul_le.trans inv_mul_le_iff_le_mul'
#align inv_le_div_iff_le_mul inv_le_div_iff_le_mul
#align neg_le_sub_iff_le_add neg_le_sub_iff_le_add

/- warning: inv_le_div_iff_le_mul' -> inv_le_div_iff_le_mul' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CommGroup.{u1} α] [_inst_2 : LE.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1))))))) (LE.le.{u1} α _inst_2)] {a : α} {b : α} {c : α}, Iff (LE.le.{u1} α _inst_2 (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1))) a) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toHasDiv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1)))) b c)) (LE.le.{u1} α _inst_2 c (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1)))))) a b))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CommGroup.{u1} α] [_inst_2 : LE.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.8394 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.8396 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1)))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.8394 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.8396) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.8409 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.8411 : α) => LE.le.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.8409 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.8411)] {a : α} {b : α} {c : α}, Iff (LE.le.{u1} α _inst_2 (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α (CommGroup.toDivisionCommMonoid.{u1} α _inst_1))))) a) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toDiv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1)))) b c)) (LE.le.{u1} α _inst_2 c (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1)))))) a b))
Case conversion may be inaccurate. Consider using '#align inv_le_div_iff_le_mul' inv_le_div_iff_le_mul'ₓ'. -/
@[to_additive]
theorem inv_le_div_iff_le_mul' : a⁻¹ ≤ b / c ↔ c ≤ a * b := by rw [inv_le_div_iff_le_mul, mul_comm]
#align inv_le_div_iff_le_mul' inv_le_div_iff_le_mul'
#align neg_le_sub_iff_le_add' neg_le_sub_iff_le_add'

/- warning: div_le_comm -> div_le_comm is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CommGroup.{u1} α] [_inst_2 : LE.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1))))))) (LE.le.{u1} α _inst_2)] {a : α} {b : α} {c : α}, Iff (LE.le.{u1} α _inst_2 (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toHasDiv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1)))) a b) c) (LE.le.{u1} α _inst_2 (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toHasDiv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1)))) a c) b)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CommGroup.{u1} α] [_inst_2 : LE.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.8490 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.8492 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1)))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.8490 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.8492) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.8505 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.8507 : α) => LE.le.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.8505 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.8507)] {a : α} {b : α} {c : α}, Iff (LE.le.{u1} α _inst_2 (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toDiv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1)))) a b) c) (LE.le.{u1} α _inst_2 (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toDiv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1)))) a c) b)
Case conversion may be inaccurate. Consider using '#align div_le_comm div_le_commₓ'. -/
@[to_additive]
theorem div_le_comm : a / b ≤ c ↔ a / c ≤ b :=
  div_le_iff_le_mul'.trans div_le_iff_le_mul.symm
#align div_le_comm div_le_comm
#align sub_le_comm sub_le_comm

/- warning: le_div_comm -> le_div_comm is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CommGroup.{u1} α] [_inst_2 : LE.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1))))))) (LE.le.{u1} α _inst_2)] {a : α} {b : α} {c : α}, Iff (LE.le.{u1} α _inst_2 a (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toHasDiv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1)))) b c)) (LE.le.{u1} α _inst_2 c (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toHasDiv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1)))) b a))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CommGroup.{u1} α] [_inst_2 : LE.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.8557 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.8559 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1)))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.8557 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.8559) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.8572 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.8574 : α) => LE.le.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.8572 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.8574)] {a : α} {b : α} {c : α}, Iff (LE.le.{u1} α _inst_2 a (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toDiv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1)))) b c)) (LE.le.{u1} α _inst_2 c (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toDiv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1)))) b a))
Case conversion may be inaccurate. Consider using '#align le_div_comm le_div_commₓ'. -/
@[to_additive]
theorem le_div_comm : a ≤ b / c ↔ c ≤ b / a :=
  le_div_iff_mul_le'.trans le_div_iff_mul_le.symm
#align le_div_comm le_div_comm
#align le_sub_comm le_sub_comm

end LE

section Preorder

variable [Preorder α] [CovariantClass α α (· * ·) (· ≤ ·)] {a b c d : α}

/- warning: div_le_div'' -> div_le_div'' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CommGroup.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1))))))) (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2))] {a : α} {b : α} {c : α} {d : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) a b) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) c d) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toHasDiv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1)))) a d) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toHasDiv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1)))) b c))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CommGroup.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.8678 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.8680 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1)))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.8678 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.8680) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.8693 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.8695 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.8693 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.8695)] {a : α} {b : α} {c : α} {d : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) a b) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) c d) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toDiv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1)))) a d) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toDiv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1)))) b c))
Case conversion may be inaccurate. Consider using '#align div_le_div'' div_le_div''ₓ'. -/
@[to_additive sub_le_sub]
theorem div_le_div'' (hab : a ≤ b) (hcd : c ≤ d) : a / d ≤ b / c :=
  by
  rw [div_eq_mul_inv, div_eq_mul_inv, mul_comm b, mul_inv_le_inv_mul_iff, mul_comm]
  exact mul_le_mul' hab hcd
#align div_le_div'' div_le_div''
#align sub_le_sub sub_le_sub

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
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LT.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.8857 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.8859 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.8857 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.8859)) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.8872 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.8874 : α) => LT.lt.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.8872 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.8874)] {a : α} {b : α} (c : α), Iff (LT.lt.{u1} α _inst_2 (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toDiv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))) a c) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toDiv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))) b c)) (LT.lt.{u1} α _inst_2 a b)
Case conversion may be inaccurate. Consider using '#align div_lt_div_iff_right div_lt_div_iff_rightₓ'. -/
@[simp, to_additive]
theorem div_lt_div_iff_right (c : α) : a / c < b / c ↔ a < b := by
  simpa only [div_eq_mul_inv] using mul_lt_mul_iff_right _
#align div_lt_div_iff_right div_lt_div_iff_right
#align sub_lt_sub_iff_right sub_lt_sub_iff_right

/- warning: div_lt_div_right' -> div_lt_div_right' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LT.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))))) (LT.lt.{u1} α _inst_2)] {a : α} {b : α}, (LT.lt.{u1} α _inst_2 a b) -> (forall (c : α), LT.lt.{u1} α _inst_2 (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toHasDiv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))) a c) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toHasDiv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))) b c))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LT.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.8935 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.8937 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.8935 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.8937)) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.8950 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.8952 : α) => LT.lt.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.8950 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.8952)] {a : α} {b : α}, (LT.lt.{u1} α _inst_2 a b) -> (forall (c : α), LT.lt.{u1} α _inst_2 (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toDiv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))) a c) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toDiv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))) b c))
Case conversion may be inaccurate. Consider using '#align div_lt_div_right' div_lt_div_right'ₓ'. -/
@[to_additive sub_lt_sub_right]
theorem div_lt_div_right' (h : a < b) (c : α) : a / c < b / c :=
  (div_lt_div_iff_right c).2 h
#align div_lt_div_right' div_lt_div_right'
#align sub_lt_sub_right sub_lt_sub_right

/- warning: one_lt_div' -> one_lt_div' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LT.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))))) (LT.lt.{u1} α _inst_2)] {a : α} {b : α}, Iff (LT.lt.{u1} α _inst_2 (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))))) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toHasDiv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))) a b)) (LT.lt.{u1} α _inst_2 b a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LT.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.9007 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.9009 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.9007 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.9009)) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.9022 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.9024 : α) => LT.lt.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.9022 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.9024)] {a : α} {b : α}, Iff (LT.lt.{u1} α _inst_2 (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (InvOneClass.toOne.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1)))))) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toDiv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))) a b)) (LT.lt.{u1} α _inst_2 b a)
Case conversion may be inaccurate. Consider using '#align one_lt_div' one_lt_div'ₓ'. -/
@[simp, to_additive sub_pos]
theorem one_lt_div' : 1 < a / b ↔ b < a := by
  rw [← mul_lt_mul_iff_right b, one_mul, div_eq_mul_inv, inv_mul_cancel_right]
#align one_lt_div' one_lt_div'
#align sub_pos sub_pos

/- warning: lt_of_sub_pos -> lt_of_sub_pos is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : AddGroup.{u1} α] [_inst_2 : LT.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α _inst_1))))))) (LT.lt.{u1} α _inst_2)] {a : α} {b : α}, (LT.lt.{u1} α _inst_2 (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α _inst_1))))))) (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α (SubNegMonoid.toHasSub.{u1} α (AddGroup.toSubNegMonoid.{u1} α _inst_1))) a b)) -> (LT.lt.{u1} α _inst_2 b a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : AddGroup.{u1} α] [_inst_2 : LT.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.9007 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.9009 : α) => HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α _inst_1))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.9007 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.9009)) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.9022 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.9024 : α) => LT.lt.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.9022 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.9024)] {a : α} {b : α}, (LT.lt.{u1} α _inst_2 (OfNat.ofNat.{u1} α 0 (Zero.toOfNat0.{u1} α (NegZeroClass.toZero.{u1} α (SubNegZeroMonoid.toNegZeroClass.{u1} α (SubtractionMonoid.toSubNegZeroMonoid.{u1} α (AddGroup.toSubtractionMonoid.{u1} α _inst_1)))))) (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α (SubNegMonoid.toSub.{u1} α (AddGroup.toSubNegMonoid.{u1} α _inst_1))) a b)) -> (LT.lt.{u1} α _inst_2 b a)
Case conversion may be inaccurate. Consider using '#align lt_of_sub_pos lt_of_sub_posₓ'. -/
/- warning: sub_pos_of_lt -> sub_pos_of_lt is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : AddGroup.{u1} α] [_inst_2 : LT.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α _inst_1))))))) (LT.lt.{u1} α _inst_2)] {a : α} {b : α}, (LT.lt.{u1} α _inst_2 b a) -> (LT.lt.{u1} α _inst_2 (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α _inst_1))))))) (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α (SubNegMonoid.toHasSub.{u1} α (AddGroup.toSubNegMonoid.{u1} α _inst_1))) a b))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : AddGroup.{u1} α] [_inst_2 : LT.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.9007 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.9009 : α) => HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α _inst_1))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.9007 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.9009)) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.9022 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.9024 : α) => LT.lt.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.9022 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.9024)] {a : α} {b : α}, (LT.lt.{u1} α _inst_2 b a) -> (LT.lt.{u1} α _inst_2 (OfNat.ofNat.{u1} α 0 (Zero.toOfNat0.{u1} α (NegZeroClass.toZero.{u1} α (SubNegZeroMonoid.toNegZeroClass.{u1} α (SubtractionMonoid.toSubNegZeroMonoid.{u1} α (AddGroup.toSubtractionMonoid.{u1} α _inst_1)))))) (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α (SubNegMonoid.toSub.{u1} α (AddGroup.toSubNegMonoid.{u1} α _inst_1))) a b))
Case conversion may be inaccurate. Consider using '#align sub_pos_of_lt sub_pos_of_ltₓ'. -/
alias sub_pos ↔ lt_of_sub_pos sub_pos_of_lt
#align lt_of_sub_pos lt_of_sub_pos
#align sub_pos_of_lt sub_pos_of_lt

/- warning: div_lt_one' -> div_lt_one' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LT.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))))) (LT.lt.{u1} α _inst_2)] {a : α} {b : α}, Iff (LT.lt.{u1} α _inst_2 (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toHasDiv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))) a b) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)))))))) (LT.lt.{u1} α _inst_2 a b)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LT.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.9108 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.9110 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.9108 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.9110)) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.9123 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.9125 : α) => LT.lt.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.9123 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.9125)] {a : α} {b : α}, Iff (LT.lt.{u1} α _inst_2 (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toDiv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))) a b) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (InvOneClass.toOne.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1))))))) (LT.lt.{u1} α _inst_2 a b)
Case conversion may be inaccurate. Consider using '#align div_lt_one' div_lt_one'ₓ'. -/
@[simp, to_additive sub_neg]
theorem div_lt_one' : a / b < 1 ↔ a < b := by
  rw [← mul_lt_mul_iff_right b, one_mul, div_eq_mul_inv, inv_mul_cancel_right]
#align div_lt_one' div_lt_one'
#align sub_neg sub_neg

/- warning: lt_of_sub_neg -> lt_of_sub_neg is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : AddGroup.{u1} α] [_inst_2 : LT.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α _inst_1))))))) (LT.lt.{u1} α _inst_2)] {a : α} {b : α}, (LT.lt.{u1} α _inst_2 (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α (SubNegMonoid.toHasSub.{u1} α (AddGroup.toSubNegMonoid.{u1} α _inst_1))) a b) (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α _inst_1)))))))) -> (LT.lt.{u1} α _inst_2 a b)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : AddGroup.{u1} α] [_inst_2 : LT.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.9108 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.9110 : α) => HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α _inst_1))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.9108 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.9110)) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.9123 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.9125 : α) => LT.lt.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.9123 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.9125)] {a : α} {b : α}, (LT.lt.{u1} α _inst_2 (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α (SubNegMonoid.toSub.{u1} α (AddGroup.toSubNegMonoid.{u1} α _inst_1))) a b) (OfNat.ofNat.{u1} α 0 (Zero.toOfNat0.{u1} α (NegZeroClass.toZero.{u1} α (SubNegZeroMonoid.toNegZeroClass.{u1} α (SubtractionMonoid.toSubNegZeroMonoid.{u1} α (AddGroup.toSubtractionMonoid.{u1} α _inst_1))))))) -> (LT.lt.{u1} α _inst_2 a b)
Case conversion may be inaccurate. Consider using '#align lt_of_sub_neg lt_of_sub_negₓ'. -/
/- warning: sub_neg_of_lt -> sub_neg_of_lt is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : AddGroup.{u1} α] [_inst_2 : LT.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α _inst_1))))))) (LT.lt.{u1} α _inst_2)] {a : α} {b : α}, (LT.lt.{u1} α _inst_2 a b) -> (LT.lt.{u1} α _inst_2 (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α (SubNegMonoid.toHasSub.{u1} α (AddGroup.toSubNegMonoid.{u1} α _inst_1))) a b) (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α _inst_1))))))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : AddGroup.{u1} α] [_inst_2 : LT.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.9108 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.9110 : α) => HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α _inst_1))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.9108 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.9110)) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.9123 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.9125 : α) => LT.lt.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.9123 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.9125)] {a : α} {b : α}, (LT.lt.{u1} α _inst_2 a b) -> (LT.lt.{u1} α _inst_2 (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α (SubNegMonoid.toSub.{u1} α (AddGroup.toSubNegMonoid.{u1} α _inst_1))) a b) (OfNat.ofNat.{u1} α 0 (Zero.toOfNat0.{u1} α (NegZeroClass.toZero.{u1} α (SubNegZeroMonoid.toNegZeroClass.{u1} α (SubtractionMonoid.toSubNegZeroMonoid.{u1} α (AddGroup.toSubtractionMonoid.{u1} α _inst_1)))))))
Case conversion may be inaccurate. Consider using '#align sub_neg_of_lt sub_neg_of_ltₓ'. -/
alias sub_neg ↔ lt_of_sub_neg sub_neg_of_lt
#align lt_of_sub_neg lt_of_sub_neg
#align sub_neg_of_lt sub_neg_of_lt

/- warning: sub_lt_zero -> sub_lt_zero is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : AddGroup.{u1} α] [_inst_2 : LT.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α _inst_1))))))) (LT.lt.{u1} α _inst_2)] {a : α} {b : α}, Iff (LT.lt.{u1} α _inst_2 (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α (SubNegMonoid.toHasSub.{u1} α (AddGroup.toSubNegMonoid.{u1} α _inst_1))) a b) (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α _inst_1)))))))) (LT.lt.{u1} α _inst_2 a b)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : AddGroup.{u1} α] [_inst_2 : LT.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.9108 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.9110 : α) => HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α _inst_1))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.9108 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.9110)) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.9123 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.9125 : α) => LT.lt.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.9123 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.9125)] {a : α} {b : α}, Iff (LT.lt.{u1} α _inst_2 (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α (SubNegMonoid.toSub.{u1} α (AddGroup.toSubNegMonoid.{u1} α _inst_1))) a b) (OfNat.ofNat.{u1} α 0 (Zero.toOfNat0.{u1} α (NegZeroClass.toZero.{u1} α (SubNegZeroMonoid.toNegZeroClass.{u1} α (SubtractionMonoid.toSubNegZeroMonoid.{u1} α (AddGroup.toSubtractionMonoid.{u1} α _inst_1))))))) (LT.lt.{u1} α _inst_2 a b)
Case conversion may be inaccurate. Consider using '#align sub_lt_zero sub_lt_zeroₓ'. -/
alias sub_neg ← sub_lt_zero
#align sub_lt_zero sub_lt_zero

/- warning: lt_div_iff_mul_lt -> lt_div_iff_mul_lt is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LT.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))))) (LT.lt.{u1} α _inst_2)] {a : α} {b : α} {c : α}, Iff (LT.lt.{u1} α _inst_2 a (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toHasDiv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))) c b)) (LT.lt.{u1} α _inst_2 (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) a b) c)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LT.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.9211 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.9213 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.9211 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.9213)) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.9226 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.9228 : α) => LT.lt.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.9226 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.9228)] {a : α} {b : α} {c : α}, Iff (LT.lt.{u1} α _inst_2 a (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toDiv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))) c b)) (LT.lt.{u1} α _inst_2 (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) a b) c)
Case conversion may be inaccurate. Consider using '#align lt_div_iff_mul_lt lt_div_iff_mul_ltₓ'. -/
@[to_additive]
theorem lt_div_iff_mul_lt : a < c / b ↔ a * b < c := by
  rw [← mul_lt_mul_iff_right b, div_eq_mul_inv, inv_mul_cancel_right]
#align lt_div_iff_mul_lt lt_div_iff_mul_lt
#align lt_sub_iff_add_lt lt_sub_iff_add_lt

/- warning: add_lt_of_lt_sub_right -> add_lt_of_lt_sub_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : AddGroup.{u1} α] [_inst_2 : LT.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α _inst_1))))))) (LT.lt.{u1} α _inst_2)] {a : α} {b : α} {c : α}, (LT.lt.{u1} α _inst_2 a (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α (SubNegMonoid.toHasSub.{u1} α (AddGroup.toSubNegMonoid.{u1} α _inst_1))) c b)) -> (LT.lt.{u1} α _inst_2 (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α _inst_1))))) a b) c)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : AddGroup.{u1} α] [_inst_2 : LT.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.9211 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.9213 : α) => HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α _inst_1))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.9211 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.9213)) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.9226 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.9228 : α) => LT.lt.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.9226 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.9228)] {a : α} {b : α} {c : α}, (LT.lt.{u1} α _inst_2 a (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α (SubNegMonoid.toSub.{u1} α (AddGroup.toSubNegMonoid.{u1} α _inst_1))) c b)) -> (LT.lt.{u1} α _inst_2 (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α _inst_1))))) a b) c)
Case conversion may be inaccurate. Consider using '#align add_lt_of_lt_sub_right add_lt_of_lt_sub_rightₓ'. -/
/- warning: lt_sub_right_of_add_lt -> lt_sub_right_of_add_lt is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : AddGroup.{u1} α] [_inst_2 : LT.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α _inst_1))))))) (LT.lt.{u1} α _inst_2)] {a : α} {b : α} {c : α}, (LT.lt.{u1} α _inst_2 (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α _inst_1))))) a b) c) -> (LT.lt.{u1} α _inst_2 a (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α (SubNegMonoid.toHasSub.{u1} α (AddGroup.toSubNegMonoid.{u1} α _inst_1))) c b))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : AddGroup.{u1} α] [_inst_2 : LT.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.9211 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.9213 : α) => HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α _inst_1))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.9211 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.9213)) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.9226 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.9228 : α) => LT.lt.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.9226 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.9228)] {a : α} {b : α} {c : α}, (LT.lt.{u1} α _inst_2 (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α _inst_1))))) a b) c) -> (LT.lt.{u1} α _inst_2 a (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α (SubNegMonoid.toSub.{u1} α (AddGroup.toSubNegMonoid.{u1} α _inst_1))) c b))
Case conversion may be inaccurate. Consider using '#align lt_sub_right_of_add_lt lt_sub_right_of_add_ltₓ'. -/
alias lt_sub_iff_add_lt ↔ add_lt_of_lt_sub_right lt_sub_right_of_add_lt
#align add_lt_of_lt_sub_right add_lt_of_lt_sub_right
#align lt_sub_right_of_add_lt lt_sub_right_of_add_lt

/- warning: div_lt_iff_lt_mul -> div_lt_iff_lt_mul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LT.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))))) (LT.lt.{u1} α _inst_2)] {a : α} {b : α} {c : α}, Iff (LT.lt.{u1} α _inst_2 (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toHasDiv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))) a c) b) (LT.lt.{u1} α _inst_2 a (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) b c))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LT.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.9313 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.9315 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.9313 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.9315)) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.9328 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.9330 : α) => LT.lt.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.9328 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.9330)] {a : α} {b : α} {c : α}, Iff (LT.lt.{u1} α _inst_2 (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toDiv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))) a c) b) (LT.lt.{u1} α _inst_2 a (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) b c))
Case conversion may be inaccurate. Consider using '#align div_lt_iff_lt_mul div_lt_iff_lt_mulₓ'. -/
@[to_additive]
theorem div_lt_iff_lt_mul : a / c < b ↔ a < b * c := by
  rw [← mul_lt_mul_iff_right c, div_eq_mul_inv, inv_mul_cancel_right]
#align div_lt_iff_lt_mul div_lt_iff_lt_mul
#align sub_lt_iff_lt_add sub_lt_iff_lt_add

/- warning: lt_add_of_sub_right_lt -> lt_add_of_sub_right_lt is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : AddGroup.{u1} α] [_inst_2 : LT.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α _inst_1))))))) (LT.lt.{u1} α _inst_2)] {a : α} {b : α} {c : α}, (LT.lt.{u1} α _inst_2 (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α (SubNegMonoid.toHasSub.{u1} α (AddGroup.toSubNegMonoid.{u1} α _inst_1))) a c) b) -> (LT.lt.{u1} α _inst_2 a (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α _inst_1))))) b c))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : AddGroup.{u1} α] [_inst_2 : LT.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.9313 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.9315 : α) => HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α _inst_1))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.9313 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.9315)) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.9328 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.9330 : α) => LT.lt.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.9328 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.9330)] {a : α} {b : α} {c : α}, (LT.lt.{u1} α _inst_2 (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α (SubNegMonoid.toSub.{u1} α (AddGroup.toSubNegMonoid.{u1} α _inst_1))) a c) b) -> (LT.lt.{u1} α _inst_2 a (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α _inst_1))))) b c))
Case conversion may be inaccurate. Consider using '#align lt_add_of_sub_right_lt lt_add_of_sub_right_ltₓ'. -/
/- warning: sub_right_lt_of_lt_add -> sub_right_lt_of_lt_add is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : AddGroup.{u1} α] [_inst_2 : LT.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α _inst_1))))))) (LT.lt.{u1} α _inst_2)] {a : α} {b : α} {c : α}, (LT.lt.{u1} α _inst_2 a (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α _inst_1))))) b c)) -> (LT.lt.{u1} α _inst_2 (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α (SubNegMonoid.toHasSub.{u1} α (AddGroup.toSubNegMonoid.{u1} α _inst_1))) a c) b)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : AddGroup.{u1} α] [_inst_2 : LT.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.9313 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.9315 : α) => HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α _inst_1))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.9313 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.9315)) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.9328 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.9330 : α) => LT.lt.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.9328 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.9330)] {a : α} {b : α} {c : α}, (LT.lt.{u1} α _inst_2 a (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α _inst_1))))) b c)) -> (LT.lt.{u1} α _inst_2 (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α (SubNegMonoid.toSub.{u1} α (AddGroup.toSubNegMonoid.{u1} α _inst_1))) a c) b)
Case conversion may be inaccurate. Consider using '#align sub_right_lt_of_lt_add sub_right_lt_of_lt_addₓ'. -/
alias sub_lt_iff_lt_add ↔ lt_add_of_sub_right_lt sub_right_lt_of_lt_add
#align lt_add_of_sub_right_lt lt_add_of_sub_right_lt
#align sub_right_lt_of_lt_add sub_right_lt_of_lt_add

end Right

section Left

variable [CovariantClass α α (· * ·) (· < ·)] [CovariantClass α α (swap (· * ·)) (· < ·)]
  {a b c : α}

/- warning: div_lt_div_iff_left -> div_lt_div_iff_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LT.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)))))) (LT.lt.{u1} α _inst_2)] [_inst_4 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))))) (LT.lt.{u1} α _inst_2)] {b : α} {c : α} (a : α), Iff (LT.lt.{u1} α _inst_2 (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toHasDiv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))) a b) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toHasDiv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))) a c)) (LT.lt.{u1} α _inst_2 c b)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LT.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.9501 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.9503 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.9501 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.9503) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.9516 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.9518 : α) => LT.lt.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.9516 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.9518)] [_inst_4 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.9538 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.9540 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.9538 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.9540)) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.9553 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.9555 : α) => LT.lt.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.9553 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.9555)] {b : α} {c : α} (a : α), Iff (LT.lt.{u1} α _inst_2 (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toDiv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))) a b) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toDiv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))) a c)) (LT.lt.{u1} α _inst_2 c b)
Case conversion may be inaccurate. Consider using '#align div_lt_div_iff_left div_lt_div_iff_leftₓ'. -/
@[simp, to_additive]
theorem div_lt_div_iff_left (a : α) : a / b < a / c ↔ c < b := by
  rw [div_eq_mul_inv, div_eq_mul_inv, ← mul_lt_mul_iff_left a⁻¹, inv_mul_cancel_left,
    inv_mul_cancel_left, inv_lt_inv_iff]
#align div_lt_div_iff_left div_lt_div_iff_left
#align sub_lt_sub_iff_left sub_lt_sub_iff_left

/- warning: inv_lt_div_iff_lt_mul -> inv_lt_div_iff_lt_mul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LT.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)))))) (LT.lt.{u1} α _inst_2)] [_inst_4 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))))) (LT.lt.{u1} α _inst_2)] {a : α} {b : α} {c : α}, Iff (LT.lt.{u1} α _inst_2 (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) a) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toHasDiv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))) b c)) (LT.lt.{u1} α _inst_2 c (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) a b))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LT.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.9640 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.9642 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.9640 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.9642) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.9655 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.9657 : α) => LT.lt.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.9655 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.9657)] [_inst_4 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.9677 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.9679 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.9677 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.9679)) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.9692 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.9694 : α) => LT.lt.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.9692 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.9694)] {a : α} {b : α} {c : α}, Iff (LT.lt.{u1} α _inst_2 (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1)))) a) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toDiv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))) b c)) (LT.lt.{u1} α _inst_2 c (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) a b))
Case conversion may be inaccurate. Consider using '#align inv_lt_div_iff_lt_mul inv_lt_div_iff_lt_mulₓ'. -/
@[simp, to_additive]
theorem inv_lt_div_iff_lt_mul : a⁻¹ < b / c ↔ c < a * b := by
  rw [div_eq_mul_inv, lt_mul_inv_iff_mul_lt, inv_mul_lt_iff_lt_mul]
#align inv_lt_div_iff_lt_mul inv_lt_div_iff_lt_mul
#align neg_lt_sub_iff_lt_add neg_lt_sub_iff_lt_add

/- warning: div_lt_div_left' -> div_lt_div_left' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LT.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)))))) (LT.lt.{u1} α _inst_2)] [_inst_4 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))))) (LT.lt.{u1} α _inst_2)] {a : α} {b : α}, (LT.lt.{u1} α _inst_2 a b) -> (forall (c : α), LT.lt.{u1} α _inst_2 (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toHasDiv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))) c b) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toHasDiv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))) c a))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LT.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.9773 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.9775 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.9773 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.9775) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.9788 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.9790 : α) => LT.lt.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.9788 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.9790)] [_inst_4 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.9810 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.9812 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.9810 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.9812)) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.9825 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.9827 : α) => LT.lt.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.9825 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.9827)] {a : α} {b : α}, (LT.lt.{u1} α _inst_2 a b) -> (forall (c : α), LT.lt.{u1} α _inst_2 (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toDiv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))) c b) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toDiv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))) c a))
Case conversion may be inaccurate. Consider using '#align div_lt_div_left' div_lt_div_left'ₓ'. -/
@[to_additive sub_lt_sub_left]
theorem div_lt_div_left' (h : a < b) (c : α) : c / b < c / a :=
  (div_lt_div_iff_left c).2 h
#align div_lt_div_left' div_lt_div_left'
#align sub_lt_sub_left sub_lt_sub_left

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
  forall {α : Type.{u1}} [_inst_1 : CommGroup.{u1} α] [_inst_2 : LT.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.9940 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.9942 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1)))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.9940 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.9942) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.9955 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.9957 : α) => LT.lt.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.9955 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.9957)] {a : α} {b : α} {c : α} {d : α}, Iff (LT.lt.{u1} α _inst_2 (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toDiv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1)))) a b) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toDiv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1)))) c d)) (LT.lt.{u1} α _inst_2 (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1)))))) a d) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1)))))) c b))
Case conversion may be inaccurate. Consider using '#align div_lt_div_iff' div_lt_div_iff'ₓ'. -/
@[to_additive sub_lt_sub_iff]
theorem div_lt_div_iff' : a / b < c / d ↔ a * d < c * b := by
  simpa only [div_eq_mul_inv] using mul_inv_lt_mul_inv_iff'
#align div_lt_div_iff' div_lt_div_iff'
#align sub_lt_sub_iff sub_lt_sub_iff

/- warning: lt_div_iff_mul_lt' -> lt_div_iff_mul_lt' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CommGroup.{u1} α] [_inst_2 : LT.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1))))))) (LT.lt.{u1} α _inst_2)] {a : α} {b : α} {c : α}, Iff (LT.lt.{u1} α _inst_2 b (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toHasDiv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1)))) c a)) (LT.lt.{u1} α _inst_2 (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1)))))) a b) c)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CommGroup.{u1} α] [_inst_2 : LT.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.10017 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.10019 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1)))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.10017 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.10019) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.10032 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.10034 : α) => LT.lt.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.10032 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.10034)] {a : α} {b : α} {c : α}, Iff (LT.lt.{u1} α _inst_2 b (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toDiv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1)))) c a)) (LT.lt.{u1} α _inst_2 (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1)))))) a b) c)
Case conversion may be inaccurate. Consider using '#align lt_div_iff_mul_lt' lt_div_iff_mul_lt'ₓ'. -/
@[to_additive]
theorem lt_div_iff_mul_lt' : b < c / a ↔ a * b < c := by rw [lt_div_iff_mul_lt, mul_comm]
#align lt_div_iff_mul_lt' lt_div_iff_mul_lt'
#align lt_sub_iff_add_lt' lt_sub_iff_add_lt'

/- warning: add_lt_of_lt_sub_left -> add_lt_of_lt_sub_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : AddCommGroup.{u1} α] [_inst_2 : LT.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_1))))))) (LT.lt.{u1} α _inst_2)] {a : α} {b : α} {c : α}, (LT.lt.{u1} α _inst_2 b (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α (SubNegMonoid.toHasSub.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_1)))) c a)) -> (LT.lt.{u1} α _inst_2 (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_1)))))) a b) c)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : AddCommGroup.{u1} α] [_inst_2 : LT.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.10017 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.10019 : α) => HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_1)))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.10017 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.10019) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.10032 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.10034 : α) => LT.lt.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.10032 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.10034)] {a : α} {b : α} {c : α}, (LT.lt.{u1} α _inst_2 b (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α (SubNegMonoid.toSub.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_1)))) c a)) -> (LT.lt.{u1} α _inst_2 (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_1)))))) a b) c)
Case conversion may be inaccurate. Consider using '#align add_lt_of_lt_sub_left add_lt_of_lt_sub_leftₓ'. -/
/- warning: lt_sub_left_of_add_lt -> lt_sub_left_of_add_lt is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : AddCommGroup.{u1} α] [_inst_2 : LT.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_1))))))) (LT.lt.{u1} α _inst_2)] {a : α} {b : α} {c : α}, (LT.lt.{u1} α _inst_2 (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_1)))))) a b) c) -> (LT.lt.{u1} α _inst_2 b (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α (SubNegMonoid.toHasSub.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_1)))) c a))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : AddCommGroup.{u1} α] [_inst_2 : LT.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.10017 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.10019 : α) => HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_1)))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.10017 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.10019) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.10032 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.10034 : α) => LT.lt.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.10032 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.10034)] {a : α} {b : α} {c : α}, (LT.lt.{u1} α _inst_2 (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_1)))))) a b) c) -> (LT.lt.{u1} α _inst_2 b (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α (SubNegMonoid.toSub.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_1)))) c a))
Case conversion may be inaccurate. Consider using '#align lt_sub_left_of_add_lt lt_sub_left_of_add_ltₓ'. -/
alias lt_sub_iff_add_lt' ↔ add_lt_of_lt_sub_left lt_sub_left_of_add_lt
#align add_lt_of_lt_sub_left add_lt_of_lt_sub_left
#align lt_sub_left_of_add_lt lt_sub_left_of_add_lt

/- warning: div_lt_iff_lt_mul' -> div_lt_iff_lt_mul' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CommGroup.{u1} α] [_inst_2 : LT.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1))))))) (LT.lt.{u1} α _inst_2)] {a : α} {b : α} {c : α}, Iff (LT.lt.{u1} α _inst_2 (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toHasDiv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1)))) a b) c) (LT.lt.{u1} α _inst_2 a (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1)))))) b c))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CommGroup.{u1} α] [_inst_2 : LT.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.10114 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.10116 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1)))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.10114 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.10116) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.10129 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.10131 : α) => LT.lt.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.10129 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.10131)] {a : α} {b : α} {c : α}, Iff (LT.lt.{u1} α _inst_2 (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toDiv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1)))) a b) c) (LT.lt.{u1} α _inst_2 a (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1)))))) b c))
Case conversion may be inaccurate. Consider using '#align div_lt_iff_lt_mul' div_lt_iff_lt_mul'ₓ'. -/
@[to_additive]
theorem div_lt_iff_lt_mul' : a / b < c ↔ a < b * c := by rw [div_lt_iff_lt_mul, mul_comm]
#align div_lt_iff_lt_mul' div_lt_iff_lt_mul'
#align sub_lt_iff_lt_add' sub_lt_iff_lt_add'

/- warning: lt_add_of_sub_left_lt -> lt_add_of_sub_left_lt is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : AddCommGroup.{u1} α] [_inst_2 : LT.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_1))))))) (LT.lt.{u1} α _inst_2)] {a : α} {b : α} {c : α}, (LT.lt.{u1} α _inst_2 (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α (SubNegMonoid.toHasSub.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_1)))) a b) c) -> (LT.lt.{u1} α _inst_2 a (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_1)))))) b c))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : AddCommGroup.{u1} α] [_inst_2 : LT.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.10114 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.10116 : α) => HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_1)))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.10114 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.10116) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.10129 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.10131 : α) => LT.lt.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.10129 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.10131)] {a : α} {b : α} {c : α}, (LT.lt.{u1} α _inst_2 (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α (SubNegMonoid.toSub.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_1)))) a b) c) -> (LT.lt.{u1} α _inst_2 a (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_1)))))) b c))
Case conversion may be inaccurate. Consider using '#align lt_add_of_sub_left_lt lt_add_of_sub_left_ltₓ'. -/
/- warning: sub_left_lt_of_lt_add -> sub_left_lt_of_lt_add is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : AddCommGroup.{u1} α] [_inst_2 : LT.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_1))))))) (LT.lt.{u1} α _inst_2)] {a : α} {b : α} {c : α}, (LT.lt.{u1} α _inst_2 a (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_1)))))) b c)) -> (LT.lt.{u1} α _inst_2 (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α (SubNegMonoid.toHasSub.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_1)))) a b) c)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : AddCommGroup.{u1} α] [_inst_2 : LT.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.10114 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.10116 : α) => HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_1)))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.10114 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.10116) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.10129 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.10131 : α) => LT.lt.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.10129 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.10131)] {a : α} {b : α} {c : α}, (LT.lt.{u1} α _inst_2 a (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_1)))))) b c)) -> (LT.lt.{u1} α _inst_2 (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α (SubNegMonoid.toSub.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_1)))) a b) c)
Case conversion may be inaccurate. Consider using '#align sub_left_lt_of_lt_add sub_left_lt_of_lt_addₓ'. -/
alias sub_lt_iff_lt_add' ↔ lt_add_of_sub_left_lt sub_left_lt_of_lt_add
#align lt_add_of_sub_left_lt lt_add_of_sub_left_lt
#align sub_left_lt_of_lt_add sub_left_lt_of_lt_add

/- warning: inv_lt_div_iff_lt_mul' -> inv_lt_div_iff_lt_mul' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CommGroup.{u1} α] [_inst_2 : LT.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1))))))) (LT.lt.{u1} α _inst_2)] {a : α} {b : α} {c : α}, Iff (LT.lt.{u1} α _inst_2 (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1))) b) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toHasDiv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1)))) a c)) (LT.lt.{u1} α _inst_2 c (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1)))))) a b))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CommGroup.{u1} α] [_inst_2 : LT.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.10211 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.10213 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1)))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.10211 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.10213) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.10226 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.10228 : α) => LT.lt.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.10226 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.10228)] {a : α} {b : α} {c : α}, Iff (LT.lt.{u1} α _inst_2 (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α (CommGroup.toDivisionCommMonoid.{u1} α _inst_1))))) b) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toDiv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1)))) a c)) (LT.lt.{u1} α _inst_2 c (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1)))))) a b))
Case conversion may be inaccurate. Consider using '#align inv_lt_div_iff_lt_mul' inv_lt_div_iff_lt_mul'ₓ'. -/
@[to_additive]
theorem inv_lt_div_iff_lt_mul' : b⁻¹ < a / c ↔ c < a * b :=
  lt_div_iff_mul_lt.trans inv_mul_lt_iff_lt_mul'
#align inv_lt_div_iff_lt_mul' inv_lt_div_iff_lt_mul'
#align neg_lt_sub_iff_lt_add' neg_lt_sub_iff_lt_add'

/- warning: div_lt_comm -> div_lt_comm is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CommGroup.{u1} α] [_inst_2 : LT.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1))))))) (LT.lt.{u1} α _inst_2)] {a : α} {b : α} {c : α}, Iff (LT.lt.{u1} α _inst_2 (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toHasDiv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1)))) a b) c) (LT.lt.{u1} α _inst_2 (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toHasDiv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1)))) a c) b)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CommGroup.{u1} α] [_inst_2 : LT.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.10280 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.10282 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1)))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.10280 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.10282) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.10295 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.10297 : α) => LT.lt.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.10295 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.10297)] {a : α} {b : α} {c : α}, Iff (LT.lt.{u1} α _inst_2 (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toDiv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1)))) a b) c) (LT.lt.{u1} α _inst_2 (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toDiv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1)))) a c) b)
Case conversion may be inaccurate. Consider using '#align div_lt_comm div_lt_commₓ'. -/
@[to_additive]
theorem div_lt_comm : a / b < c ↔ a / c < b :=
  div_lt_iff_lt_mul'.trans div_lt_iff_lt_mul.symm
#align div_lt_comm div_lt_comm
#align sub_lt_comm sub_lt_comm

/- warning: lt_div_comm -> lt_div_comm is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CommGroup.{u1} α] [_inst_2 : LT.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1))))))) (LT.lt.{u1} α _inst_2)] {a : α} {b : α} {c : α}, Iff (LT.lt.{u1} α _inst_2 a (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toHasDiv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1)))) b c)) (LT.lt.{u1} α _inst_2 c (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toHasDiv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1)))) b a))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CommGroup.{u1} α] [_inst_2 : LT.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.10347 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.10349 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1)))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.10347 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.10349) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.10362 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.10364 : α) => LT.lt.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.10362 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.10364)] {a : α} {b : α} {c : α}, Iff (LT.lt.{u1} α _inst_2 a (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toDiv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1)))) b c)) (LT.lt.{u1} α _inst_2 c (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toDiv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1)))) b a))
Case conversion may be inaccurate. Consider using '#align lt_div_comm lt_div_commₓ'. -/
@[to_additive]
theorem lt_div_comm : a < b / c ↔ c < b / a :=
  lt_div_iff_mul_lt'.trans lt_div_iff_mul_lt.symm
#align lt_div_comm lt_div_comm
#align lt_sub_comm lt_sub_comm

end LT

section Preorder

variable [Preorder α] [CovariantClass α α (· * ·) (· < ·)] {a b c d : α}

/- warning: div_lt_div'' -> div_lt_div'' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CommGroup.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1))))))) (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2))] {a : α} {b : α} {c : α} {d : α}, (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) a b) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) c d) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toHasDiv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1)))) a d) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toHasDiv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1)))) b c))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CommGroup.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.10468 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.10470 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1)))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.10468 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.10470) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.10483 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.10485 : α) => LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.10483 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.10485)] {a : α} {b : α} {c : α} {d : α}, (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) a b) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) c d) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toDiv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1)))) a d) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toDiv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1)))) b c))
Case conversion may be inaccurate. Consider using '#align div_lt_div'' div_lt_div''ₓ'. -/
@[to_additive sub_lt_sub]
theorem div_lt_div'' (hab : a < b) (hcd : c < d) : a / d < b / c :=
  by
  rw [div_eq_mul_inv, div_eq_mul_inv, mul_comm b, mul_inv_lt_inv_mul_iff, mul_comm]
  exact mul_lt_mul_of_lt_of_lt hab hcd
#align div_lt_div'' div_lt_div''
#align sub_lt_sub sub_lt_sub

end Preorder

end CommGroup

section LinearOrder

variable [Group α] [LinearOrder α]

/- warning: cmp_div_one' -> cmp_div_one' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LinearOrder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))))) (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_2))))))] (a : α) (b : α), Eq.{1} Ordering (cmp.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_2))))) (fun (a : α) (b : α) => LT.lt.decidable.{u1} α _inst_2 a b) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toHasDiv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))) a b) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)))))))) (cmp.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_2))))) (fun (a : α) (b : α) => LT.lt.decidable.{u1} α _inst_2 a b) a b)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LinearOrder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.10592 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.10594 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.10592 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.10594)) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.10607 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.10609 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_2)))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.10607 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.10609)] (a : α) (b : α), Eq.{1} Ordering (cmp.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_2)))))) (fun (a : α) (b : α) => instDecidableLtToLTToPreorderToPartialOrder.{u1} α _inst_2 a b) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toDiv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))) a b) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (InvOneClass.toOne.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1))))))) (cmp.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_2)))))) (fun (a : α) (b : α) => instDecidableLtToLTToPreorderToPartialOrder.{u1} α _inst_2 a b) a b)
Case conversion may be inaccurate. Consider using '#align cmp_div_one' cmp_div_one'ₓ'. -/
@[simp, to_additive cmp_sub_zero]
theorem cmp_div_one' [CovariantClass α α (swap (· * ·)) (· ≤ ·)] (a b : α) :
    cmp (a / b) 1 = cmp a b := by rw [← cmp_mul_right' _ _ b, one_mul, div_mul_cancel']
#align cmp_div_one' cmp_div_one'
#align cmp_sub_zero cmp_sub_zero

variable [CovariantClass α α (· * ·) (· ≤ ·)]

section VariableNames

variable {a b c : α}

/- warning: le_of_forall_one_lt_lt_mul -> le_of_forall_one_lt_lt_mul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LinearOrder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)))))) (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_2))))))] {a : α} {b : α}, (forall (ε : α), (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_2))))) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))))) ε) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_2))))) a (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) b ε))) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_2))))) a b)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LinearOrder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.10779 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.10781 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.10779 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.10781) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.10794 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.10796 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_2)))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.10794 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.10796)] {a : α} {b : α}, (forall (ε : α), (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_2)))))) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (InvOneClass.toOne.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1)))))) ε) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_2)))))) a (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) b ε))) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_2)))))) a b)
Case conversion may be inaccurate. Consider using '#align le_of_forall_one_lt_lt_mul le_of_forall_one_lt_lt_mulₓ'. -/
@[to_additive]
theorem le_of_forall_one_lt_lt_mul (h : ∀ ε : α, 1 < ε → a < b * ε) : a ≤ b :=
  le_of_not_lt fun h₁ => lt_irrefl a (by simpa using h _ (lt_inv_mul_iff_lt.mpr h₁))
#align le_of_forall_one_lt_lt_mul le_of_forall_one_lt_lt_mul
#align le_of_forall_pos_lt_add le_of_forall_pos_lt_add

/- warning: le_iff_forall_one_lt_lt_mul -> le_iff_forall_one_lt_lt_mul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LinearOrder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)))))) (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_2))))))] {a : α} {b : α}, Iff (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_2))))) a b) (forall (ε : α), (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_2))))) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))))) ε) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_2))))) a (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) b ε)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LinearOrder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.10868 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.10870 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.10868 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.10870) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.10883 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.10885 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_2)))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.10883 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.10885)] {a : α} {b : α}, Iff (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_2)))))) a b) (forall (ε : α), (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_2)))))) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (InvOneClass.toOne.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1)))))) ε) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_2)))))) a (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) b ε)))
Case conversion may be inaccurate. Consider using '#align le_iff_forall_one_lt_lt_mul le_iff_forall_one_lt_lt_mulₓ'. -/
@[to_additive]
theorem le_iff_forall_one_lt_lt_mul : a ≤ b ↔ ∀ ε, 1 < ε → a < b * ε :=
  ⟨fun h ε => lt_mul_of_le_of_one_lt h, le_of_forall_one_lt_lt_mul⟩
#align le_iff_forall_one_lt_lt_mul le_iff_forall_one_lt_lt_mul
#align le_iff_forall_pos_lt_add le_iff_forall_pos_lt_add

/- warning: div_le_inv_mul_iff -> div_le_inv_mul_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LinearOrder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)))))) (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_2))))))] {a : α} {b : α} [_inst_4 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))))) (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_2))))))], Iff (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_2))))) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toHasDiv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))) a b) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) a) b)) (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_2))))) a b)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : LinearOrder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.10949 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.10951 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.10949 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.10951) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.10964 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.10966 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_2)))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.10964 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.10966)] {a : α} {b : α} [_inst_4 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.10989 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.10991 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.10989 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.10991)) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.11004 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.11006 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_2)))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.11004 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.11006)], Iff (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_2)))))) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toDiv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))) a b) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1)))) a) b)) (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_2)))))) a b)
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
#align sub_le_neg_add_iff sub_le_neg_add_iff

/- warning: div_le_div_flip -> div_le_div_flip is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_4 : CommGroup.{u1} α] [_inst_5 : LinearOrder.{u1} α] [_inst_6 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_4))))))) (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_5))))))] {a : α} {b : α}, Iff (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_5))))) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toHasDiv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_4)))) a b) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toHasDiv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_4)))) b a)) (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_5))))) a b)
but is expected to have type
  forall {α : Type.{u1}} [_inst_4 : CommGroup.{u1} α] [_inst_5 : LinearOrder.{u1} α] [_inst_6 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.11152 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.11154 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_4)))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.11152 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.11154) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.11167 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.11169 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_5)))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.11167 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.11169)] {a : α} {b : α}, Iff (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_5)))))) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toDiv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_4)))) a b) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toDiv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_4)))) b a)) (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_5)))))) a b)
Case conversion may be inaccurate. Consider using '#align div_le_div_flip div_le_div_flipₓ'. -/
--  What is the point of this lemma?  See comment about `div_le_inv_mul_iff` above.
@[simp, to_additive]
theorem div_le_div_flip {α : Type _} [CommGroup α] [LinearOrder α]
    [CovariantClass α α (· * ·) (· ≤ ·)] {a b : α} : a / b ≤ b / a ↔ a ≤ b :=
  by
  rw [div_eq_mul_inv b, mul_comm]
  exact div_le_inv_mul_iff
#align div_le_div_flip div_le_div_flip
#align sub_le_sub_flip sub_le_sub_flip

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
#align linear_ordered_add_comm_group LinearOrderedAddCommGroup
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
#align linear_ordered_add_comm_group.add_lt_add_left LinearOrderedAddCommGroup.add_lt_add_left

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
#align eq_zero_of_neg_eq eq_zero_of_neg_eq

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
#align exists_zero_lt exists_zero_lt

#print LinearOrderedCommGroup.to_noMaxOrder /-
-- see Note [lower instance priority]
@[to_additive]
instance (priority := 100) LinearOrderedCommGroup.to_noMaxOrder [Nontrivial α] : NoMaxOrder α :=
  ⟨by
    obtain ⟨y, hy⟩ : ∃ a : α, 1 < a := exists_one_lt'
    exact fun a => ⟨a * y, lt_mul_of_one_lt_right' a hy⟩⟩
#align linear_ordered_comm_group.to_no_max_order LinearOrderedCommGroup.to_noMaxOrder
#align linear_ordered_add_comm_group.to_no_max_order LinearOrderedAddCommGroup.to_noMaxOrder
-/

#print LinearOrderedCommGroup.to_noMinOrder /-
-- see Note [lower instance priority]
@[to_additive]
instance (priority := 100) LinearOrderedCommGroup.to_noMinOrder [Nontrivial α] : NoMinOrder α :=
  ⟨by
    obtain ⟨y, hy⟩ : ∃ a : α, 1 < a := exists_one_lt'
    exact fun a => ⟨a / y, (div_lt_self_iff a).mpr hy⟩⟩
#align linear_ordered_comm_group.to_no_min_order LinearOrderedCommGroup.to_noMinOrder
#align linear_ordered_add_comm_group.to_no_min_order LinearOrderedAddCommGroup.to_noMinOrder
-/

#print LinearOrderedCommGroup.toLinearOrderedCancelCommMonoid /-
-- See note [lower instance priority]
@[to_additive]
instance (priority := 100) LinearOrderedCommGroup.toLinearOrderedCancelCommMonoid :
    LinearOrderedCancelCommMonoid α :=
  { ‹LinearOrderedCommGroup α›, OrderedCommGroup.toOrderedCancelCommMonoid with }
#align linear_ordered_comm_group.to_linear_ordered_cancel_comm_monoid LinearOrderedCommGroup.toLinearOrderedCancelCommMonoid
#align linear_ordered_add_comm_group.to_linear_ordered_cancel_add_comm_monoid LinearOrderedAddCommGroup.toLinearOrderedAddCancelCommMonoid
-/

end LinearOrderedCommGroup

namespace AddCommGroup

#print AddCommGroup.PositiveCone /-
/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic order_laws_tac -/
/-- A collection of elements in an `add_comm_group` designated as "non-negative".
This is useful for constructing an `ordered_add_commm_group`
by choosing a positive cone in an exisiting `add_comm_group`. -/
@[nolint has_nonempty_instance]
structure PositiveCone (α : Type _) [AddCommGroup α] where
  NonNeg : α → Prop
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
    le := fun a b => C.NonNeg (b - a)
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
#align neg_le_neg neg_le_neg

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
#align neg_lt_neg neg_lt_neg

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
#align neg_neg_of_pos neg_neg_of_pos

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
#align neg_nonpos_of_nonneg neg_nonpos_of_nonneg

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
#align neg_nonneg_of_nonpos neg_nonneg_of_nonpos

end NormNumLemmas

section

variable {β : Type _} [Group α] [Preorder α] [CovariantClass α α (· * ·) (· ≤ ·)]
  [CovariantClass α α (swap (· * ·)) (· ≤ ·)] [Preorder β] {f : β → α} {s : Set β}

/- warning: monotone.inv -> Monotone.inv is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Group.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)))))) (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2))] [_inst_4 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))))) (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2))] [_inst_5 : Preorder.{u2} β] {f : β -> α}, (Monotone.{u2, u1} β α _inst_5 _inst_2 f) -> (Antitone.{u2, u1} β α _inst_5 _inst_2 (fun (x : β) => Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) (f x)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Group.{u2} α] [_inst_2 : Preorder.{u2} α] [_inst_3 : CovariantClass.{u2, u2} α α (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.12542 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.12544 : α) => HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α (MulOneClass.toMul.{u2} α (Monoid.toMulOneClass.{u2} α (DivInvMonoid.toMonoid.{u2} α (Group.toDivInvMonoid.{u2} α _inst_1))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.12542 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.12544) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.12557 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.12559 : α) => LE.le.{u2} α (Preorder.toLE.{u2} α _inst_2) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.12557 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.12559)] [_inst_4 : CovariantClass.{u2, u2} α α (Function.swap.{succ u2, succ u2, succ u2} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.12579 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.12581 : α) => HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α (MulOneClass.toMul.{u2} α (Monoid.toMulOneClass.{u2} α (DivInvMonoid.toMonoid.{u2} α (Group.toDivInvMonoid.{u2} α _inst_1))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.12579 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.12581)) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.12594 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.12596 : α) => LE.le.{u2} α (Preorder.toLE.{u2} α _inst_2) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.12594 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.12596)] [_inst_5 : Preorder.{u1} β] {f : β -> α}, (Monotone.{u1, u2} β α _inst_5 _inst_2 f) -> (Antitone.{u1, u2} β α _inst_5 _inst_2 (fun (x : β) => Inv.inv.{u2} α (InvOneClass.toInv.{u2} α (DivInvOneMonoid.toInvOneClass.{u2} α (DivisionMonoid.toDivInvOneMonoid.{u2} α (Group.toDivisionMonoid.{u2} α _inst_1)))) (f x)))
Case conversion may be inaccurate. Consider using '#align monotone.inv Monotone.invₓ'. -/
@[to_additive]
theorem Monotone.inv (hf : Monotone f) : Antitone fun x => (f x)⁻¹ := fun x y hxy =>
  inv_le_inv_iff.2 (hf hxy)
#align monotone.inv Monotone.inv
#align monotone.neg Monotone.neg

/- warning: antitone.inv -> Antitone.inv is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Group.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)))))) (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2))] [_inst_4 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))))) (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2))] [_inst_5 : Preorder.{u2} β] {f : β -> α}, (Antitone.{u2, u1} β α _inst_5 _inst_2 f) -> (Monotone.{u2, u1} β α _inst_5 _inst_2 (fun (x : β) => Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) (f x)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Group.{u2} α] [_inst_2 : Preorder.{u2} α] [_inst_3 : CovariantClass.{u2, u2} α α (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.12661 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.12663 : α) => HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α (MulOneClass.toMul.{u2} α (Monoid.toMulOneClass.{u2} α (DivInvMonoid.toMonoid.{u2} α (Group.toDivInvMonoid.{u2} α _inst_1))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.12661 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.12663) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.12676 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.12678 : α) => LE.le.{u2} α (Preorder.toLE.{u2} α _inst_2) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.12676 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.12678)] [_inst_4 : CovariantClass.{u2, u2} α α (Function.swap.{succ u2, succ u2, succ u2} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.12698 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.12700 : α) => HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α (MulOneClass.toMul.{u2} α (Monoid.toMulOneClass.{u2} α (DivInvMonoid.toMonoid.{u2} α (Group.toDivInvMonoid.{u2} α _inst_1))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.12698 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.12700)) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.12713 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.12715 : α) => LE.le.{u2} α (Preorder.toLE.{u2} α _inst_2) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.12713 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.12715)] [_inst_5 : Preorder.{u1} β] {f : β -> α}, (Antitone.{u1, u2} β α _inst_5 _inst_2 f) -> (Monotone.{u1, u2} β α _inst_5 _inst_2 (fun (x : β) => Inv.inv.{u2} α (InvOneClass.toInv.{u2} α (DivInvOneMonoid.toInvOneClass.{u2} α (DivisionMonoid.toDivInvOneMonoid.{u2} α (Group.toDivisionMonoid.{u2} α _inst_1)))) (f x)))
Case conversion may be inaccurate. Consider using '#align antitone.inv Antitone.invₓ'. -/
@[to_additive]
theorem Antitone.inv (hf : Antitone f) : Monotone fun x => (f x)⁻¹ := fun x y hxy =>
  inv_le_inv_iff.2 (hf hxy)
#align antitone.inv Antitone.inv
#align antitone.neg Antitone.neg

/- warning: monotone_on.inv -> MonotoneOn.inv is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Group.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)))))) (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2))] [_inst_4 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))))) (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2))] [_inst_5 : Preorder.{u2} β] {f : β -> α} {s : Set.{u2} β}, (MonotoneOn.{u2, u1} β α _inst_5 _inst_2 f s) -> (AntitoneOn.{u2, u1} β α _inst_5 _inst_2 (fun (x : β) => Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) (f x)) s)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Group.{u2} α] [_inst_2 : Preorder.{u2} α] [_inst_3 : CovariantClass.{u2, u2} α α (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.12780 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.12782 : α) => HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α (MulOneClass.toMul.{u2} α (Monoid.toMulOneClass.{u2} α (DivInvMonoid.toMonoid.{u2} α (Group.toDivInvMonoid.{u2} α _inst_1))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.12780 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.12782) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.12795 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.12797 : α) => LE.le.{u2} α (Preorder.toLE.{u2} α _inst_2) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.12795 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.12797)] [_inst_4 : CovariantClass.{u2, u2} α α (Function.swap.{succ u2, succ u2, succ u2} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.12817 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.12819 : α) => HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α (MulOneClass.toMul.{u2} α (Monoid.toMulOneClass.{u2} α (DivInvMonoid.toMonoid.{u2} α (Group.toDivInvMonoid.{u2} α _inst_1))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.12817 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.12819)) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.12832 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.12834 : α) => LE.le.{u2} α (Preorder.toLE.{u2} α _inst_2) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.12832 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.12834)] [_inst_5 : Preorder.{u1} β] {f : β -> α} {s : Set.{u1} β}, (MonotoneOn.{u1, u2} β α _inst_5 _inst_2 f s) -> (AntitoneOn.{u1, u2} β α _inst_5 _inst_2 (fun (x : β) => Inv.inv.{u2} α (InvOneClass.toInv.{u2} α (DivInvOneMonoid.toInvOneClass.{u2} α (DivisionMonoid.toDivInvOneMonoid.{u2} α (Group.toDivisionMonoid.{u2} α _inst_1)))) (f x)) s)
Case conversion may be inaccurate. Consider using '#align monotone_on.inv MonotoneOn.invₓ'. -/
@[to_additive]
theorem MonotoneOn.inv (hf : MonotoneOn f s) : AntitoneOn (fun x => (f x)⁻¹) s :=
  fun x hx y hy hxy => inv_le_inv_iff.2 (hf hx hy hxy)
#align monotone_on.inv MonotoneOn.inv
#align monotone_on.neg MonotoneOn.neg

/- warning: antitone_on.inv -> AntitoneOn.inv is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Group.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)))))) (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2))] [_inst_4 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))))) (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2))] [_inst_5 : Preorder.{u2} β] {f : β -> α} {s : Set.{u2} β}, (AntitoneOn.{u2, u1} β α _inst_5 _inst_2 f s) -> (MonotoneOn.{u2, u1} β α _inst_5 _inst_2 (fun (x : β) => Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) (f x)) s)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Group.{u2} α] [_inst_2 : Preorder.{u2} α] [_inst_3 : CovariantClass.{u2, u2} α α (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.12907 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.12909 : α) => HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α (MulOneClass.toMul.{u2} α (Monoid.toMulOneClass.{u2} α (DivInvMonoid.toMonoid.{u2} α (Group.toDivInvMonoid.{u2} α _inst_1))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.12907 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.12909) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.12922 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.12924 : α) => LE.le.{u2} α (Preorder.toLE.{u2} α _inst_2) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.12922 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.12924)] [_inst_4 : CovariantClass.{u2, u2} α α (Function.swap.{succ u2, succ u2, succ u2} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.12944 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.12946 : α) => HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α (MulOneClass.toMul.{u2} α (Monoid.toMulOneClass.{u2} α (DivInvMonoid.toMonoid.{u2} α (Group.toDivInvMonoid.{u2} α _inst_1))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.12944 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.12946)) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.12959 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.12961 : α) => LE.le.{u2} α (Preorder.toLE.{u2} α _inst_2) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.12959 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.12961)] [_inst_5 : Preorder.{u1} β] {f : β -> α} {s : Set.{u1} β}, (AntitoneOn.{u1, u2} β α _inst_5 _inst_2 f s) -> (MonotoneOn.{u1, u2} β α _inst_5 _inst_2 (fun (x : β) => Inv.inv.{u2} α (InvOneClass.toInv.{u2} α (DivInvOneMonoid.toInvOneClass.{u2} α (DivisionMonoid.toDivInvOneMonoid.{u2} α (Group.toDivisionMonoid.{u2} α _inst_1)))) (f x)) s)
Case conversion may be inaccurate. Consider using '#align antitone_on.inv AntitoneOn.invₓ'. -/
@[to_additive]
theorem AntitoneOn.inv (hf : AntitoneOn f s) : MonotoneOn (fun x => (f x)⁻¹) s :=
  fun x hx y hy hxy => inv_le_inv_iff.2 (hf hx hy hxy)
#align antitone_on.inv AntitoneOn.inv
#align antitone_on.neg AntitoneOn.neg

end

section

variable {β : Type _} [Group α] [Preorder α] [CovariantClass α α (· * ·) (· < ·)]
  [CovariantClass α α (swap (· * ·)) (· < ·)] [Preorder β] {f : β → α} {s : Set β}

/- warning: strict_mono.inv -> StrictMono.inv is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Group.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)))))) (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2))] [_inst_4 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))))) (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2))] [_inst_5 : Preorder.{u2} β] {f : β -> α}, (StrictMono.{u2, u1} β α _inst_5 _inst_2 f) -> (StrictAnti.{u2, u1} β α _inst_5 _inst_2 (fun (x : β) => Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) (f x)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Group.{u2} α] [_inst_2 : Preorder.{u2} α] [_inst_3 : CovariantClass.{u2, u2} α α (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.13132 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.13134 : α) => HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α (MulOneClass.toMul.{u2} α (Monoid.toMulOneClass.{u2} α (DivInvMonoid.toMonoid.{u2} α (Group.toDivInvMonoid.{u2} α _inst_1))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.13132 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.13134) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.13147 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.13149 : α) => LT.lt.{u2} α (Preorder.toLT.{u2} α _inst_2) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.13147 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.13149)] [_inst_4 : CovariantClass.{u2, u2} α α (Function.swap.{succ u2, succ u2, succ u2} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.13169 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.13171 : α) => HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α (MulOneClass.toMul.{u2} α (Monoid.toMulOneClass.{u2} α (DivInvMonoid.toMonoid.{u2} α (Group.toDivInvMonoid.{u2} α _inst_1))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.13169 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.13171)) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.13184 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.13186 : α) => LT.lt.{u2} α (Preorder.toLT.{u2} α _inst_2) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.13184 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.13186)] [_inst_5 : Preorder.{u1} β] {f : β -> α}, (StrictMono.{u1, u2} β α _inst_5 _inst_2 f) -> (StrictAnti.{u1, u2} β α _inst_5 _inst_2 (fun (x : β) => Inv.inv.{u2} α (InvOneClass.toInv.{u2} α (DivInvOneMonoid.toInvOneClass.{u2} α (DivisionMonoid.toDivInvOneMonoid.{u2} α (Group.toDivisionMonoid.{u2} α _inst_1)))) (f x)))
Case conversion may be inaccurate. Consider using '#align strict_mono.inv StrictMono.invₓ'. -/
@[to_additive]
theorem StrictMono.inv (hf : StrictMono f) : StrictAnti fun x => (f x)⁻¹ := fun x y hxy =>
  inv_lt_inv_iff.2 (hf hxy)
#align strict_mono.inv StrictMono.inv
#align strict_mono.neg StrictMono.neg

/- warning: strict_anti.inv -> StrictAnti.inv is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Group.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)))))) (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2))] [_inst_4 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))))) (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2))] [_inst_5 : Preorder.{u2} β] {f : β -> α}, (StrictAnti.{u2, u1} β α _inst_5 _inst_2 f) -> (StrictMono.{u2, u1} β α _inst_5 _inst_2 (fun (x : β) => Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) (f x)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Group.{u2} α] [_inst_2 : Preorder.{u2} α] [_inst_3 : CovariantClass.{u2, u2} α α (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.13251 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.13253 : α) => HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α (MulOneClass.toMul.{u2} α (Monoid.toMulOneClass.{u2} α (DivInvMonoid.toMonoid.{u2} α (Group.toDivInvMonoid.{u2} α _inst_1))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.13251 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.13253) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.13266 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.13268 : α) => LT.lt.{u2} α (Preorder.toLT.{u2} α _inst_2) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.13266 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.13268)] [_inst_4 : CovariantClass.{u2, u2} α α (Function.swap.{succ u2, succ u2, succ u2} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.13288 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.13290 : α) => HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α (MulOneClass.toMul.{u2} α (Monoid.toMulOneClass.{u2} α (DivInvMonoid.toMonoid.{u2} α (Group.toDivInvMonoid.{u2} α _inst_1))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.13288 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.13290)) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.13303 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.13305 : α) => LT.lt.{u2} α (Preorder.toLT.{u2} α _inst_2) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.13303 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.13305)] [_inst_5 : Preorder.{u1} β] {f : β -> α}, (StrictAnti.{u1, u2} β α _inst_5 _inst_2 f) -> (StrictMono.{u1, u2} β α _inst_5 _inst_2 (fun (x : β) => Inv.inv.{u2} α (InvOneClass.toInv.{u2} α (DivInvOneMonoid.toInvOneClass.{u2} α (DivisionMonoid.toDivInvOneMonoid.{u2} α (Group.toDivisionMonoid.{u2} α _inst_1)))) (f x)))
Case conversion may be inaccurate. Consider using '#align strict_anti.inv StrictAnti.invₓ'. -/
@[to_additive]
theorem StrictAnti.inv (hf : StrictAnti f) : StrictMono fun x => (f x)⁻¹ := fun x y hxy =>
  inv_lt_inv_iff.2 (hf hxy)
#align strict_anti.inv StrictAnti.inv
#align strict_anti.neg StrictAnti.neg

/- warning: strict_mono_on.inv -> StrictMonoOn.inv is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Group.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)))))) (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2))] [_inst_4 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))))) (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2))] [_inst_5 : Preorder.{u2} β] {f : β -> α} {s : Set.{u2} β}, (StrictMonoOn.{u2, u1} β α _inst_5 _inst_2 f s) -> (StrictAntiOn.{u2, u1} β α _inst_5 _inst_2 (fun (x : β) => Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) (f x)) s)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Group.{u2} α] [_inst_2 : Preorder.{u2} α] [_inst_3 : CovariantClass.{u2, u2} α α (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.13370 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.13372 : α) => HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α (MulOneClass.toMul.{u2} α (Monoid.toMulOneClass.{u2} α (DivInvMonoid.toMonoid.{u2} α (Group.toDivInvMonoid.{u2} α _inst_1))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.13370 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.13372) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.13385 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.13387 : α) => LT.lt.{u2} α (Preorder.toLT.{u2} α _inst_2) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.13385 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.13387)] [_inst_4 : CovariantClass.{u2, u2} α α (Function.swap.{succ u2, succ u2, succ u2} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.13407 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.13409 : α) => HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α (MulOneClass.toMul.{u2} α (Monoid.toMulOneClass.{u2} α (DivInvMonoid.toMonoid.{u2} α (Group.toDivInvMonoid.{u2} α _inst_1))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.13407 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.13409)) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.13422 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.13424 : α) => LT.lt.{u2} α (Preorder.toLT.{u2} α _inst_2) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.13422 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.13424)] [_inst_5 : Preorder.{u1} β] {f : β -> α} {s : Set.{u1} β}, (StrictMonoOn.{u1, u2} β α _inst_5 _inst_2 f s) -> (StrictAntiOn.{u1, u2} β α _inst_5 _inst_2 (fun (x : β) => Inv.inv.{u2} α (InvOneClass.toInv.{u2} α (DivInvOneMonoid.toInvOneClass.{u2} α (DivisionMonoid.toDivInvOneMonoid.{u2} α (Group.toDivisionMonoid.{u2} α _inst_1)))) (f x)) s)
Case conversion may be inaccurate. Consider using '#align strict_mono_on.inv StrictMonoOn.invₓ'. -/
@[to_additive]
theorem StrictMonoOn.inv (hf : StrictMonoOn f s) : StrictAntiOn (fun x => (f x)⁻¹) s :=
  fun x hx y hy hxy => inv_lt_inv_iff.2 (hf hx hy hxy)
#align strict_mono_on.inv StrictMonoOn.inv
#align strict_mono_on.neg StrictMonoOn.neg

/- warning: strict_anti_on.inv -> StrictAntiOn.inv is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Group.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)))))) (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2))] [_inst_4 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))))) (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2))] [_inst_5 : Preorder.{u2} β] {f : β -> α} {s : Set.{u2} β}, (StrictAntiOn.{u2, u1} β α _inst_5 _inst_2 f s) -> (StrictMonoOn.{u2, u1} β α _inst_5 _inst_2 (fun (x : β) => Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) (f x)) s)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Group.{u2} α] [_inst_2 : Preorder.{u2} α] [_inst_3 : CovariantClass.{u2, u2} α α (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.13497 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.13499 : α) => HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α (MulOneClass.toMul.{u2} α (Monoid.toMulOneClass.{u2} α (DivInvMonoid.toMonoid.{u2} α (Group.toDivInvMonoid.{u2} α _inst_1))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.13497 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.13499) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.13512 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.13514 : α) => LT.lt.{u2} α (Preorder.toLT.{u2} α _inst_2) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.13512 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.13514)] [_inst_4 : CovariantClass.{u2, u2} α α (Function.swap.{succ u2, succ u2, succ u2} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.13534 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.13536 : α) => HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α (MulOneClass.toMul.{u2} α (Monoid.toMulOneClass.{u2} α (DivInvMonoid.toMonoid.{u2} α (Group.toDivInvMonoid.{u2} α _inst_1))))) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.13534 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.13536)) (fun (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.13549 : α) (x._@.Mathlib.Algebra.Order.Group.Defs._hyg.13551 : α) => LT.lt.{u2} α (Preorder.toLT.{u2} α _inst_2) x._@.Mathlib.Algebra.Order.Group.Defs._hyg.13549 x._@.Mathlib.Algebra.Order.Group.Defs._hyg.13551)] [_inst_5 : Preorder.{u1} β] {f : β -> α} {s : Set.{u1} β}, (StrictAntiOn.{u1, u2} β α _inst_5 _inst_2 f s) -> (StrictMonoOn.{u1, u2} β α _inst_5 _inst_2 (fun (x : β) => Inv.inv.{u2} α (InvOneClass.toInv.{u2} α (DivInvOneMonoid.toInvOneClass.{u2} α (DivisionMonoid.toDivInvOneMonoid.{u2} α (Group.toDivisionMonoid.{u2} α _inst_1)))) (f x)) s)
Case conversion may be inaccurate. Consider using '#align strict_anti_on.inv StrictAntiOn.invₓ'. -/
@[to_additive]
theorem StrictAntiOn.inv (hf : StrictAntiOn f s) : StrictMonoOn (fun x => (f x)⁻¹) s :=
  fun x hx y hy hxy => inv_lt_inv_iff.2 (hf hx hy hxy)
#align strict_anti_on.inv StrictAntiOn.inv
#align strict_anti_on.neg StrictAntiOn.neg

end

