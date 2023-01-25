/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro, Johannes Hölzl

! This file was ported from Lean 3 source module algebra.order.monoid.with_zero.defs
! leanprover-community/mathlib commit e3d9ab8faa9dea8f78155c6c27d62a621f4c152d
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Group.WithOne.Defs
import Mathbin.Algebra.Order.Monoid.Canonical.Defs
import Mathbin.Algebra.Order.ZeroLeOne

/-!
# Adjoining a zero element to an ordered monoid.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.
-/


universe u

variable {α : Type u}

#print LinearOrderedCommMonoidWithZero /-
/-- A linearly ordered commutative monoid with a zero element. -/
class LinearOrderedCommMonoidWithZero (α : Type _) extends LinearOrderedCommMonoid α,
  CommMonoidWithZero α where
  zero_le_one : (0 : α) ≤ 1
#align linear_ordered_comm_monoid_with_zero LinearOrderedCommMonoidWithZero
-/

/- warning: linear_ordered_comm_monoid_with_zero.to_zero_le_one_class -> LinearOrderedCommMonoidWithZero.toZeroLeOneClass is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : LinearOrderedCommMonoidWithZero.{u1} α], ZeroLEOneClass.{u1} α (MulZeroClass.toHasZero.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (LinearOrderedCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))))) (MulOneClass.toHasOne.{u1} α (MulZeroOneClass.toMulOneClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (LinearOrderedCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))))) (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommMonoid.toPartialOrder.{u1} α (LinearOrderedCommMonoid.toOrderedCommMonoid.{u1} α (LinearOrderedCommMonoidWithZero.toLinearOrderedCommMonoid.{u1} α _inst_1)))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : LinearOrderedCommMonoidWithZero.{u1} α], ZeroLEOneClass.{u1} α (LinearOrderedCommMonoidWithZero.toZero.{u1} α _inst_1) (Monoid.toOne.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (LinearOrderedCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1)))) (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommMonoid.toPartialOrder.{u1} α (LinearOrderedCommMonoid.toOrderedCommMonoid.{u1} α (LinearOrderedCommMonoidWithZero.toLinearOrderedCommMonoid.{u1} α _inst_1)))))
Case conversion may be inaccurate. Consider using '#align linear_ordered_comm_monoid_with_zero.to_zero_le_one_class LinearOrderedCommMonoidWithZero.toZeroLeOneClassₓ'. -/
instance (priority := 100) LinearOrderedCommMonoidWithZero.toZeroLeOneClass
    [LinearOrderedCommMonoidWithZero α] : ZeroLEOneClass α :=
  { ‹LinearOrderedCommMonoidWithZero α› with }
#align linear_ordered_comm_monoid_with_zero.to_zero_le_one_class LinearOrderedCommMonoidWithZero.toZeroLeOneClass

/- warning: canonically_ordered_add_monoid.to_zero_le_one_class -> CanonicallyOrderedAddMonoid.toZeroLeOneClass is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CanonicallyOrderedAddMonoid.{u1} α] [_inst_2 : One.{u1} α], ZeroLEOneClass.{u1} α (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α (OrderedAddCommMonoid.toAddCommMonoid.{u1} α (CanonicallyOrderedAddMonoid.toOrderedAddCommMonoid.{u1} α _inst_1))))) _inst_2 (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedAddCommMonoid.toPartialOrder.{u1} α (CanonicallyOrderedAddMonoid.toOrderedAddCommMonoid.{u1} α _inst_1))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CanonicallyOrderedAddMonoid.{u1} α] [_inst_2 : One.{u1} α], ZeroLEOneClass.{u1} α (AddMonoid.toZero.{u1} α (AddCommMonoid.toAddMonoid.{u1} α (OrderedAddCommMonoid.toAddCommMonoid.{u1} α (CanonicallyOrderedAddMonoid.toOrderedAddCommMonoid.{u1} α _inst_1)))) _inst_2 (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedAddCommMonoid.toPartialOrder.{u1} α (CanonicallyOrderedAddMonoid.toOrderedAddCommMonoid.{u1} α _inst_1))))
Case conversion may be inaccurate. Consider using '#align canonically_ordered_add_monoid.to_zero_le_one_class CanonicallyOrderedAddMonoid.toZeroLeOneClassₓ'. -/
instance (priority := 100) CanonicallyOrderedAddMonoid.toZeroLeOneClass
    [CanonicallyOrderedAddMonoid α] [One α] : ZeroLEOneClass α :=
  ⟨zero_le 1⟩
#align canonically_ordered_add_monoid.to_zero_le_one_class CanonicallyOrderedAddMonoid.toZeroLeOneClass

namespace WithZero

attribute [local semireducible] WithZero

instance [Preorder α] : Preorder (WithZero α) :=
  WithBot.preorder

instance [PartialOrder α] : PartialOrder (WithZero α) :=
  WithBot.partialOrder

instance [Preorder α] : OrderBot (WithZero α) :=
  WithBot.orderBot

#print WithZero.zero_le /-
theorem zero_le [Preorder α] (a : WithZero α) : 0 ≤ a :=
  bot_le
#align with_zero.zero_le WithZero.zero_le
-/

#print WithZero.zero_lt_coe /-
theorem zero_lt_coe [Preorder α] (a : α) : (0 : WithZero α) < a :=
  WithBot.bot_lt_coe a
#align with_zero.zero_lt_coe WithZero.zero_lt_coe
-/

/- warning: with_zero.zero_eq_bot -> WithZero.zero_eq_bot is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α], Eq.{succ u1} (WithZero.{u1} α) (OfNat.ofNat.{u1} (WithZero.{u1} α) 0 (OfNat.mk.{u1} (WithZero.{u1} α) 0 (Zero.zero.{u1} (WithZero.{u1} α) (WithZero.zero.{u1} α)))) (Bot.bot.{u1} (WithZero.{u1} α) (OrderBot.toHasBot.{u1} (WithZero.{u1} α) (Preorder.toLE.{u1} (WithZero.{u1} α) (WithZero.preorder.{u1} α _inst_1)) (WithZero.orderBot.{u1} α _inst_1)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α], Eq.{succ u1} (WithZero.{u1} α) (OfNat.ofNat.{u1} (WithZero.{u1} α) 0 (Zero.toOfNat0.{u1} (WithZero.{u1} α) (WithZero.zero.{u1} α))) (Bot.bot.{u1} (WithZero.{u1} α) (OrderBot.toBot.{u1} (WithZero.{u1} α) (Preorder.toLE.{u1} (WithZero.{u1} α) (WithZero.preorder.{u1} α _inst_1)) (WithZero.orderBot.{u1} α _inst_1)))
Case conversion may be inaccurate. Consider using '#align with_zero.zero_eq_bot WithZero.zero_eq_botₓ'. -/
theorem zero_eq_bot [Preorder α] : (0 : WithZero α) = ⊥ :=
  rfl
#align with_zero.zero_eq_bot WithZero.zero_eq_bot

#print WithZero.coe_lt_coe /-
@[simp, norm_cast]
theorem coe_lt_coe [Preorder α] {a b : α} : (a : WithZero α) < b ↔ a < b :=
  WithBot.coe_lt_coe
#align with_zero.coe_lt_coe WithZero.coe_lt_coe
-/

#print WithZero.coe_le_coe /-
@[simp, norm_cast]
theorem coe_le_coe [Preorder α] {a b : α} : (a : WithZero α) ≤ b ↔ a ≤ b :=
  WithBot.coe_le_coe
#align with_zero.coe_le_coe WithZero.coe_le_coe
-/

instance [Lattice α] : Lattice (WithZero α) :=
  WithBot.lattice

instance [LinearOrder α] : LinearOrder (WithZero α) :=
  WithBot.linearOrder

/- warning: with_zero.covariant_class_mul_le -> WithZero.covariantClass_mul_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Mul.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1)) (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2))], CovariantClass.{u1, u1} (WithZero.{u1} α) (WithZero.{u1} α) (HMul.hMul.{u1, u1, u1} (WithZero.{u1} α) (WithZero.{u1} α) (WithZero.{u1} α) (instHMul.{u1} (WithZero.{u1} α) (MulZeroClass.toHasMul.{u1} (WithZero.{u1} α) (WithZero.mulZeroClass.{u1} α _inst_1)))) (LE.le.{u1} (WithZero.{u1} α) (Preorder.toLE.{u1} (WithZero.{u1} α) (WithZero.preorder.{u1} α _inst_2)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Mul.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.WithZero.Defs._hyg.257 : α) (x._@.Mathlib.Algebra.Order.Monoid.WithZero.Defs._hyg.259 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1) x._@.Mathlib.Algebra.Order.Monoid.WithZero.Defs._hyg.257 x._@.Mathlib.Algebra.Order.Monoid.WithZero.Defs._hyg.259) (fun (x._@.Mathlib.Algebra.Order.Monoid.WithZero.Defs._hyg.272 : α) (x._@.Mathlib.Algebra.Order.Monoid.WithZero.Defs._hyg.274 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.WithZero.Defs._hyg.272 x._@.Mathlib.Algebra.Order.Monoid.WithZero.Defs._hyg.274)], CovariantClass.{u1, u1} (WithZero.{u1} α) (WithZero.{u1} α) (fun (x._@.Mathlib.Algebra.Order.Monoid.WithZero.Defs._hyg.296 : WithZero.{u1} α) (x._@.Mathlib.Algebra.Order.Monoid.WithZero.Defs._hyg.298 : WithZero.{u1} α) => HMul.hMul.{u1, u1, u1} (WithZero.{u1} α) (WithZero.{u1} α) (WithZero.{u1} α) (instHMul.{u1} (WithZero.{u1} α) (MulZeroClass.toMul.{u1} (WithZero.{u1} α) (WithZero.mulZeroClass.{u1} α _inst_1))) x._@.Mathlib.Algebra.Order.Monoid.WithZero.Defs._hyg.296 x._@.Mathlib.Algebra.Order.Monoid.WithZero.Defs._hyg.298) (fun (x._@.Mathlib.Algebra.Order.Monoid.WithZero.Defs._hyg.311 : WithZero.{u1} α) (x._@.Mathlib.Algebra.Order.Monoid.WithZero.Defs._hyg.313 : WithZero.{u1} α) => LE.le.{u1} (WithZero.{u1} α) (Preorder.toLE.{u1} (WithZero.{u1} α) (WithZero.preorder.{u1} α _inst_2)) x._@.Mathlib.Algebra.Order.Monoid.WithZero.Defs._hyg.311 x._@.Mathlib.Algebra.Order.Monoid.WithZero.Defs._hyg.313)
Case conversion may be inaccurate. Consider using '#align with_zero.covariant_class_mul_le WithZero.covariantClass_mul_leₓ'. -/
instance covariantClass_mul_le {α : Type u} [Mul α] [Preorder α]
    [CovariantClass α α (· * ·) (· ≤ ·)] :
    CovariantClass (WithZero α) (WithZero α) (· * ·) (· ≤ ·) :=
  by
  refine' ⟨fun a b c hbc => _⟩
  induction a using WithZero.recZeroCoe; · exact zero_le _
  induction b using WithZero.recZeroCoe; · exact zero_le _
  rcases WithBot.coe_le_iff.1 hbc with ⟨c, rfl, hbc'⟩
  rw [← coe_mul, ← coe_mul, coe_le_coe]
  exact mul_le_mul_left' hbc' a
#align with_zero.covariant_class_mul_le WithZero.covariantClass_mul_le

/- warning: with_zero.le_max_iff clashes with [anonymous] -> [anonymous]
warning: with_zero.le_max_iff -> [anonymous] is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} [_inst_1 : LinearOrder.{u} α] {a : α} {b : α} {c : α}, Iff (LE.le.{u} (WithZero.{u} α) (Preorder.toLE.{u} (WithZero.{u} α) (WithZero.preorder.{u} α (PartialOrder.toPreorder.{u} α (SemilatticeInf.toPartialOrder.{u} α (Lattice.toSemilatticeInf.{u} α (LinearOrder.toLattice.{u} α _inst_1)))))) ((fun (a : Type.{u}) (b : Type.{u}) [self : HasLiftT.{succ u, succ u} a b] => self.0) α (WithZero.{u} α) (HasLiftT.mk.{succ u, succ u} α (WithZero.{u} α) (CoeTCₓ.coe.{succ u, succ u} α (WithZero.{u} α) (WithZero.hasCoeT.{u} α))) a) (LinearOrder.max.{u} (WithZero.{u} α) (WithZero.linearOrder.{u} α _inst_1) ((fun (a : Type.{u}) (b : Type.{u}) [self : HasLiftT.{succ u, succ u} a b] => self.0) α (WithZero.{u} α) (HasLiftT.mk.{succ u, succ u} α (WithZero.{u} α) (CoeTCₓ.coe.{succ u, succ u} α (WithZero.{u} α) (WithZero.hasCoeT.{u} α))) b) ((fun (a : Type.{u}) (b : Type.{u}) [self : HasLiftT.{succ u, succ u} a b] => self.0) α (WithZero.{u} α) (HasLiftT.mk.{succ u, succ u} α (WithZero.{u} α) (CoeTCₓ.coe.{succ u, succ u} α (WithZero.{u} α) (WithZero.hasCoeT.{u} α))) c))) (LE.le.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α (SemilatticeInf.toPartialOrder.{u} α (Lattice.toSemilatticeInf.{u} α (LinearOrder.toLattice.{u} α _inst_1))))) a (LinearOrder.max.{u} α _inst_1 b c))
but is expected to have type
  forall {α : Type.{u}} {_inst_1 : Type.{v}}, (Nat -> α -> _inst_1) -> Nat -> (List.{u} α) -> (List.{v} _inst_1)
Case conversion may be inaccurate. Consider using '#align with_zero.le_max_iff [anonymous]ₓ'. -/
@[simp]
theorem [anonymous] [LinearOrder α] {a b c : α} : (a : WithZero α) ≤ max b c ↔ a ≤ max b c := by
  simp only [WithZero.coe_le_coe, le_max_iff]
#align with_zero.le_max_iff [anonymous]

/- warning: with_zero.min_le_iff clashes with [anonymous] -> [anonymous]
warning: with_zero.min_le_iff -> [anonymous] is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} [_inst_1 : LinearOrder.{u} α] {a : α} {b : α} {c : α}, Iff (LE.le.{u} (WithZero.{u} α) (Preorder.toLE.{u} (WithZero.{u} α) (WithZero.preorder.{u} α (PartialOrder.toPreorder.{u} α (SemilatticeInf.toPartialOrder.{u} α (Lattice.toSemilatticeInf.{u} α (LinearOrder.toLattice.{u} α _inst_1)))))) (LinearOrder.min.{u} (WithZero.{u} α) (WithZero.linearOrder.{u} α _inst_1) ((fun (a : Type.{u}) (b : Type.{u}) [self : HasLiftT.{succ u, succ u} a b] => self.0) α (WithZero.{u} α) (HasLiftT.mk.{succ u, succ u} α (WithZero.{u} α) (CoeTCₓ.coe.{succ u, succ u} α (WithZero.{u} α) (WithZero.hasCoeT.{u} α))) a) ((fun (a : Type.{u}) (b : Type.{u}) [self : HasLiftT.{succ u, succ u} a b] => self.0) α (WithZero.{u} α) (HasLiftT.mk.{succ u, succ u} α (WithZero.{u} α) (CoeTCₓ.coe.{succ u, succ u} α (WithZero.{u} α) (WithZero.hasCoeT.{u} α))) b)) ((fun (a : Type.{u}) (b : Type.{u}) [self : HasLiftT.{succ u, succ u} a b] => self.0) α (WithZero.{u} α) (HasLiftT.mk.{succ u, succ u} α (WithZero.{u} α) (CoeTCₓ.coe.{succ u, succ u} α (WithZero.{u} α) (WithZero.hasCoeT.{u} α))) c)) (LE.le.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α (SemilatticeInf.toPartialOrder.{u} α (Lattice.toSemilatticeInf.{u} α (LinearOrder.toLattice.{u} α _inst_1))))) (LinearOrder.min.{u} α _inst_1 a b) c)
but is expected to have type
  forall {α : Type.{u}} {_inst_1 : Type.{v}}, (Nat -> α -> _inst_1) -> Nat -> (List.{u} α) -> (List.{v} _inst_1)
Case conversion may be inaccurate. Consider using '#align with_zero.min_le_iff [anonymous]ₓ'. -/
@[simp]
theorem [anonymous] [LinearOrder α] {a b c : α} : min (a : WithZero α) b ≤ c ↔ min a b ≤ c := by
  simp only [WithZero.coe_le_coe, min_le_iff]
#align with_zero.min_le_iff [anonymous]

instance [OrderedCommMonoid α] : OrderedCommMonoid (WithZero α) :=
  { WithZero.commMonoidWithZero, WithZero.partialOrder with
    mul_le_mul_left := fun _ _ => mul_le_mul_left' }

/- warning: with_zero.covariant_class_add_le -> WithZero.covariantClass_add_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : AddZeroClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toHasAdd.{u1} α _inst_1))) (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2))], (forall (a : α), LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (AddZeroClass.toHasZero.{u1} α _inst_1)))) a) -> (CovariantClass.{u1, u1} (WithZero.{u1} α) (WithZero.{u1} α) (HAdd.hAdd.{u1, u1, u1} (WithZero.{u1} α) (WithZero.{u1} α) (WithZero.{u1} α) (instHAdd.{u1} (WithZero.{u1} α) (WithZero.add.{u1} α (AddZeroClass.toHasAdd.{u1} α _inst_1)))) (LE.le.{u1} (WithZero.{u1} α) (Preorder.toLE.{u1} (WithZero.{u1} α) (WithZero.preorder.{u1} α _inst_2))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : AddZeroClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.WithZero.Defs._hyg.456 : α) (x._@.Mathlib.Algebra.Order.Monoid.WithZero.Defs._hyg.458 : α) => HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toAdd.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.WithZero.Defs._hyg.456 x._@.Mathlib.Algebra.Order.Monoid.WithZero.Defs._hyg.458) (fun (x._@.Mathlib.Algebra.Order.Monoid.WithZero.Defs._hyg.471 : α) (x._@.Mathlib.Algebra.Order.Monoid.WithZero.Defs._hyg.473 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.WithZero.Defs._hyg.471 x._@.Mathlib.Algebra.Order.Monoid.WithZero.Defs._hyg.473)], (forall (a : α), LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) (OfNat.ofNat.{u1} α 0 (Zero.toOfNat0.{u1} α (AddZeroClass.toZero.{u1} α _inst_1))) a) -> (CovariantClass.{u1, u1} (WithZero.{u1} α) (WithZero.{u1} α) (fun (x._@.Mathlib.Algebra.Order.Monoid.WithZero.Defs._hyg.505 : WithZero.{u1} α) (x._@.Mathlib.Algebra.Order.Monoid.WithZero.Defs._hyg.507 : WithZero.{u1} α) => HAdd.hAdd.{u1, u1, u1} (WithZero.{u1} α) (WithZero.{u1} α) (WithZero.{u1} α) (instHAdd.{u1} (WithZero.{u1} α) (WithZero.add.{u1} α (AddZeroClass.toAdd.{u1} α _inst_1))) x._@.Mathlib.Algebra.Order.Monoid.WithZero.Defs._hyg.505 x._@.Mathlib.Algebra.Order.Monoid.WithZero.Defs._hyg.507) (fun (x._@.Mathlib.Algebra.Order.Monoid.WithZero.Defs._hyg.520 : WithZero.{u1} α) (x._@.Mathlib.Algebra.Order.Monoid.WithZero.Defs._hyg.522 : WithZero.{u1} α) => LE.le.{u1} (WithZero.{u1} α) (Preorder.toLE.{u1} (WithZero.{u1} α) (WithZero.preorder.{u1} α _inst_2)) x._@.Mathlib.Algebra.Order.Monoid.WithZero.Defs._hyg.520 x._@.Mathlib.Algebra.Order.Monoid.WithZero.Defs._hyg.522))
Case conversion may be inaccurate. Consider using '#align with_zero.covariant_class_add_le WithZero.covariantClass_add_leₓ'. -/
protected theorem covariantClass_add_le [AddZeroClass α] [Preorder α]
    [CovariantClass α α (· + ·) (· ≤ ·)] (h : ∀ a : α, 0 ≤ a) :
    CovariantClass (WithZero α) (WithZero α) (· + ·) (· ≤ ·) :=
  by
  refine' ⟨fun a b c hbc => _⟩
  induction a using WithZero.recZeroCoe
  · rwa [zero_add, zero_add]
  induction b using WithZero.recZeroCoe
  · rw [add_zero]
    induction c using WithZero.recZeroCoe
    · rw [add_zero]
      exact le_rfl
    · rw [← coe_add, coe_le_coe]
      exact le_add_of_nonneg_right (h _)
  · rcases WithBot.coe_le_iff.1 hbc with ⟨c, rfl, hbc'⟩
    rw [← coe_add, ← coe_add, coe_le_coe]
    exact add_le_add_left hbc' a
#align with_zero.covariant_class_add_le WithZero.covariantClass_add_le

/- warning: with_zero.ordered_add_comm_monoid -> WithZero.orderedAddCommMonoid is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : OrderedAddCommMonoid.{u1} α], (forall (a : α), LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedAddCommMonoid.toPartialOrder.{u1} α _inst_1))) (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α (OrderedAddCommMonoid.toAddCommMonoid.{u1} α _inst_1))))))) a) -> (OrderedAddCommMonoid.{u1} (WithZero.{u1} α))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : OrderedAddCommMonoid.{u1} α], (forall (a : α), LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedAddCommMonoid.toPartialOrder.{u1} α _inst_1))) (OfNat.ofNat.{u1} α 0 (Zero.toOfNat0.{u1} α (AddMonoid.toZero.{u1} α (AddCommMonoid.toAddMonoid.{u1} α (OrderedAddCommMonoid.toAddCommMonoid.{u1} α _inst_1))))) a) -> (OrderedAddCommMonoid.{u1} (WithZero.{u1} α))
Case conversion may be inaccurate. Consider using '#align with_zero.ordered_add_comm_monoid WithZero.orderedAddCommMonoidₓ'. -/
/-
Note 1 : the below is not an instance because it requires `zero_le`. It seems
like a rather pathological definition because α already has a zero.
Note 2 : there is no multiplicative analogue because it does not seem necessary.
Mathematicians might be more likely to use the order-dual version, where all
elements are ≤ 1 and then 1 is the top element.
-/
/-- If `0` is the least element in `α`, then `with_zero α` is an `ordered_add_comm_monoid`.
See note [reducible non-instances].
-/
@[reducible]
protected def orderedAddCommMonoid [OrderedAddCommMonoid α] (zero_le : ∀ a : α, 0 ≤ a) :
    OrderedAddCommMonoid (WithZero α) :=
  { WithZero.partialOrder, WithZero.addCommMonoid with
    add_le_add_left := @add_le_add_left _ _ _ (WithZero.covariantClass_add_le zero_le).. }
#align with_zero.ordered_add_comm_monoid WithZero.orderedAddCommMonoid

end WithZero

section CanonicallyOrderedMonoid

#print WithZero.existsAddOfLE /-
instance WithZero.existsAddOfLE {α} [Add α] [Preorder α] [ExistsAddOfLE α] :
    ExistsAddOfLE (WithZero α) :=
  ⟨fun a b => by
    apply WithZero.cases_on a
    · exact fun _ => ⟨b, (zero_add b).symm⟩
    apply WithZero.cases_on b
    · exact fun b' h => (WithBot.not_coe_le_bot _ h).elim
    rintro a' b' h
    obtain ⟨c, rfl⟩ := exists_add_of_le (WithZero.coe_le_coe.1 h)
    exact ⟨c, rfl⟩⟩
#align with_zero.has_exists_add_of_le WithZero.existsAddOfLE
-/

#print WithZero.canonicallyOrderedAddMonoid /-
-- This instance looks absurd: a monoid already has a zero
/-- Adding a new zero to a canonically ordered additive monoid produces another one. -/
instance WithZero.canonicallyOrderedAddMonoid {α : Type u} [CanonicallyOrderedAddMonoid α] :
    CanonicallyOrderedAddMonoid (WithZero α) :=
  { WithZero.orderBot, WithZero.orderedAddCommMonoid zero_le, WithZero.existsAddOfLE with
    le_self_add := fun a b => by
      apply WithZero.cases_on a
      · exact bot_le
      apply WithZero.cases_on b
      · exact fun b' => le_rfl
      · exact fun a' b' => WithZero.coe_le_coe.2 le_self_add }
#align with_zero.canonically_ordered_add_monoid WithZero.canonicallyOrderedAddMonoid
-/

end CanonicallyOrderedMonoid

section CanonicallyLinearOrderedMonoid

#print WithZero.canonicallyLinearOrderedAddMonoid /-
instance WithZero.canonicallyLinearOrderedAddMonoid (α : Type _)
    [CanonicallyLinearOrderedAddMonoid α] : CanonicallyLinearOrderedAddMonoid (WithZero α) :=
  { WithZero.canonicallyOrderedAddMonoid, WithZero.linearOrder with }
#align with_zero.canonically_linear_ordered_add_monoid WithZero.canonicallyLinearOrderedAddMonoid
-/

end CanonicallyLinearOrderedMonoid

