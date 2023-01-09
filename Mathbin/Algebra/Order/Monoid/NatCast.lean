/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro, Johannes Hölzl, Yuyang Zhao

! This file was ported from Lean 3 source module algebra.order.monoid.nat_cast
! leanprover-community/mathlib commit 247a102b14f3cebfee126293341af5f6bed00237
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Order.Monoid.Lemmas
import Mathbin.Algebra.Order.ZeroLeOne
import Mathbin.Data.Nat.Cast.Defs

/-!
# Order of numerials in an `add_monoid_with_one`.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.
-/


variable {α : Type _}

open Function

/- warning: lt_add_one -> lt_add_one is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : One.{u1} α] [_inst_2 : AddZeroClass.{u1} α] [_inst_3 : PartialOrder.{u1} α] [_inst_4 : ZeroLEOneClass.{u1} α (AddZeroClass.toHasZero.{u1} α _inst_2) _inst_1 (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_3))] [_inst_5 : NeZero.{u1} α (AddZeroClass.toHasZero.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α _inst_1)))] [_inst_6 : CovariantClass.{u1, u1} α α (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toHasAdd.{u1} α _inst_2))) (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α _inst_3)))] (a : α), LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α _inst_3)) a (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toHasAdd.{u1} α _inst_2)) a (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α _inst_1))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : One.{u1} α] [_inst_2 : AddZeroClass.{u1} α] [_inst_3 : PartialOrder.{u1} α] [_inst_4 : ZeroLEOneClass.{u1} α (AddZeroClass.toZero.{u1} α _inst_2) _inst_1 (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_3))] [_inst_5 : NeZero.{u1} α (AddZeroClass.toZero.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α _inst_1))] [_inst_6 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.NatCast._hyg.36 : α) (x._@.Mathlib.Algebra.Order.Monoid.NatCast._hyg.38 : α) => HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toAdd.{u1} α _inst_2)) x._@.Mathlib.Algebra.Order.Monoid.NatCast._hyg.36 x._@.Mathlib.Algebra.Order.Monoid.NatCast._hyg.38) (fun (x._@.Mathlib.Algebra.Order.Monoid.NatCast._hyg.51 : α) (x._@.Mathlib.Algebra.Order.Monoid.NatCast._hyg.53 : α) => LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α _inst_3)) x._@.Mathlib.Algebra.Order.Monoid.NatCast._hyg.51 x._@.Mathlib.Algebra.Order.Monoid.NatCast._hyg.53)] (a : α), LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α _inst_3)) a (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toAdd.{u1} α _inst_2)) a (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α _inst_1)))
Case conversion may be inaccurate. Consider using '#align lt_add_one lt_add_oneₓ'. -/
theorem lt_add_one [One α] [AddZeroClass α] [PartialOrder α] [ZeroLEOneClass α] [NeZero (1 : α)]
    [CovariantClass α α (· + ·) (· < ·)] (a : α) : a < a + 1 :=
  lt_add_of_pos_right _ zero_lt_one
#align lt_add_one lt_add_one

/- warning: lt_one_add -> lt_one_add is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : One.{u1} α] [_inst_2 : AddZeroClass.{u1} α] [_inst_3 : PartialOrder.{u1} α] [_inst_4 : ZeroLEOneClass.{u1} α (AddZeroClass.toHasZero.{u1} α _inst_2) _inst_1 (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_3))] [_inst_5 : NeZero.{u1} α (AddZeroClass.toHasZero.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α _inst_1)))] [_inst_6 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toHasAdd.{u1} α _inst_2)))) (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α _inst_3)))] (a : α), LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α _inst_3)) a (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toHasAdd.{u1} α _inst_2)) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α _inst_1))) a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : One.{u1} α] [_inst_2 : AddZeroClass.{u1} α] [_inst_3 : PartialOrder.{u1} α] [_inst_4 : ZeroLEOneClass.{u1} α (AddZeroClass.toZero.{u1} α _inst_2) _inst_1 (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_3))] [_inst_5 : NeZero.{u1} α (AddZeroClass.toZero.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α _inst_1))] [_inst_6 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.NatCast._hyg.106 : α) (x._@.Mathlib.Algebra.Order.Monoid.NatCast._hyg.108 : α) => HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toAdd.{u1} α _inst_2)) x._@.Mathlib.Algebra.Order.Monoid.NatCast._hyg.106 x._@.Mathlib.Algebra.Order.Monoid.NatCast._hyg.108)) (fun (x._@.Mathlib.Algebra.Order.Monoid.NatCast._hyg.121 : α) (x._@.Mathlib.Algebra.Order.Monoid.NatCast._hyg.123 : α) => LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α _inst_3)) x._@.Mathlib.Algebra.Order.Monoid.NatCast._hyg.121 x._@.Mathlib.Algebra.Order.Monoid.NatCast._hyg.123)] (a : α), LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α _inst_3)) a (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toAdd.{u1} α _inst_2)) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α _inst_1)) a)
Case conversion may be inaccurate. Consider using '#align lt_one_add lt_one_addₓ'. -/
theorem lt_one_add [One α] [AddZeroClass α] [PartialOrder α] [ZeroLEOneClass α] [NeZero (1 : α)]
    [CovariantClass α α (swap (· + ·)) (· < ·)] (a : α) : a < 1 + a :=
  lt_add_of_pos_left _ zero_lt_one
#align lt_one_add lt_one_add

variable [AddMonoidWithOne α]

/- warning: zero_le_two -> zero_le_two is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : AddMonoidWithOne.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : ZeroLEOneClass.{u1} α (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddMonoidWithOne.toAddMonoid.{u1} α _inst_1))) (AddMonoidWithOne.toOne.{u1} α _inst_1) (Preorder.toLE.{u1} α _inst_2)] [_inst_4 : CovariantClass.{u1, u1} α α (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddMonoidWithOne.toAddMonoid.{u1} α _inst_1))))) (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2))], LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddMonoidWithOne.toAddMonoid.{u1} α _inst_1)))))) (OfNat.ofNat.{u1} α 2 (OfNat.mk.{u1} α 2 (bit0.{u1} α (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddMonoidWithOne.toAddMonoid.{u1} α _inst_1))) (One.one.{u1} α (AddMonoidWithOne.toOne.{u1} α _inst_1)))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : AddMonoidWithOne.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : ZeroLEOneClass.{u1} α (AddMonoid.toZero.{u1} α (AddMonoidWithOne.toAddMonoid.{u1} α _inst_1)) (AddMonoidWithOne.toOne.{u1} α _inst_1) (Preorder.toLE.{u1} α _inst_2)] [_inst_4 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.NatCast._hyg.170 : α) (x._@.Mathlib.Algebra.Order.Monoid.NatCast._hyg.172 : α) => HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddMonoidWithOne.toAddMonoid.{u1} α _inst_1)))) x._@.Mathlib.Algebra.Order.Monoid.NatCast._hyg.170 x._@.Mathlib.Algebra.Order.Monoid.NatCast._hyg.172) (fun (x._@.Mathlib.Algebra.Order.Monoid.NatCast._hyg.185 : α) (x._@.Mathlib.Algebra.Order.Monoid.NatCast._hyg.187 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.NatCast._hyg.185 x._@.Mathlib.Algebra.Order.Monoid.NatCast._hyg.187)], LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) (OfNat.ofNat.{u1} α 0 (Zero.toOfNat0.{u1} α (AddMonoid.toZero.{u1} α (AddMonoidWithOne.toAddMonoid.{u1} α _inst_1)))) (OfNat.ofNat.{u1} α 2 (instOfNat.{u1} α 2 (AddMonoidWithOne.toNatCast.{u1} α _inst_1) (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)))))
Case conversion may be inaccurate. Consider using '#align zero_le_two zero_le_twoₓ'. -/
theorem zero_le_two [Preorder α] [ZeroLEOneClass α] [CovariantClass α α (· + ·) (· ≤ ·)] :
    (0 : α) ≤ 2 :=
  add_nonneg zero_le_one zero_le_one
#align zero_le_two zero_le_two

/- warning: zero_le_three -> zero_le_three is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : AddMonoidWithOne.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : ZeroLEOneClass.{u1} α (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddMonoidWithOne.toAddMonoid.{u1} α _inst_1))) (AddMonoidWithOne.toOne.{u1} α _inst_1) (Preorder.toLE.{u1} α _inst_2)] [_inst_4 : CovariantClass.{u1, u1} α α (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddMonoidWithOne.toAddMonoid.{u1} α _inst_1))))) (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2))], LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddMonoidWithOne.toAddMonoid.{u1} α _inst_1)))))) (OfNat.ofNat.{u1} α 3 (OfNat.mk.{u1} α 3 (bit1.{u1} α (AddMonoidWithOne.toOne.{u1} α _inst_1) (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddMonoidWithOne.toAddMonoid.{u1} α _inst_1))) (One.one.{u1} α (AddMonoidWithOne.toOne.{u1} α _inst_1)))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : AddMonoidWithOne.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : ZeroLEOneClass.{u1} α (AddMonoid.toZero.{u1} α (AddMonoidWithOne.toAddMonoid.{u1} α _inst_1)) (AddMonoidWithOne.toOne.{u1} α _inst_1) (Preorder.toLE.{u1} α _inst_2)] [_inst_4 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.NatCast._hyg.262 : α) (x._@.Mathlib.Algebra.Order.Monoid.NatCast._hyg.264 : α) => HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddMonoidWithOne.toAddMonoid.{u1} α _inst_1)))) x._@.Mathlib.Algebra.Order.Monoid.NatCast._hyg.262 x._@.Mathlib.Algebra.Order.Monoid.NatCast._hyg.264) (fun (x._@.Mathlib.Algebra.Order.Monoid.NatCast._hyg.277 : α) (x._@.Mathlib.Algebra.Order.Monoid.NatCast._hyg.279 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.NatCast._hyg.277 x._@.Mathlib.Algebra.Order.Monoid.NatCast._hyg.279)], LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) (OfNat.ofNat.{u1} α 0 (Zero.toOfNat0.{u1} α (AddMonoid.toZero.{u1} α (AddMonoidWithOne.toAddMonoid.{u1} α _inst_1)))) (OfNat.ofNat.{u1} α 3 (instOfNat.{u1} α 3 (AddMonoidWithOne.toNatCast.{u1} α _inst_1) (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))))
Case conversion may be inaccurate. Consider using '#align zero_le_three zero_le_threeₓ'. -/
theorem zero_le_three [Preorder α] [ZeroLEOneClass α] [CovariantClass α α (· + ·) (· ≤ ·)] :
    (0 : α) ≤ 3 :=
  add_nonneg zero_le_two zero_le_one
#align zero_le_three zero_le_three

/- warning: zero_le_four -> zero_le_four is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : AddMonoidWithOne.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : ZeroLEOneClass.{u1} α (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddMonoidWithOne.toAddMonoid.{u1} α _inst_1))) (AddMonoidWithOne.toOne.{u1} α _inst_1) (Preorder.toLE.{u1} α _inst_2)] [_inst_4 : CovariantClass.{u1, u1} α α (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddMonoidWithOne.toAddMonoid.{u1} α _inst_1))))) (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2))], LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddMonoidWithOne.toAddMonoid.{u1} α _inst_1)))))) (OfNat.ofNat.{u1} α 4 (OfNat.mk.{u1} α 4 (bit0.{u1} α (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddMonoidWithOne.toAddMonoid.{u1} α _inst_1))) (bit0.{u1} α (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddMonoidWithOne.toAddMonoid.{u1} α _inst_1))) (One.one.{u1} α (AddMonoidWithOne.toOne.{u1} α _inst_1))))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : AddMonoidWithOne.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : ZeroLEOneClass.{u1} α (AddMonoid.toZero.{u1} α (AddMonoidWithOne.toAddMonoid.{u1} α _inst_1)) (AddMonoidWithOne.toOne.{u1} α _inst_1) (Preorder.toLE.{u1} α _inst_2)] [_inst_4 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.NatCast._hyg.354 : α) (x._@.Mathlib.Algebra.Order.Monoid.NatCast._hyg.356 : α) => HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddMonoidWithOne.toAddMonoid.{u1} α _inst_1)))) x._@.Mathlib.Algebra.Order.Monoid.NatCast._hyg.354 x._@.Mathlib.Algebra.Order.Monoid.NatCast._hyg.356) (fun (x._@.Mathlib.Algebra.Order.Monoid.NatCast._hyg.369 : α) (x._@.Mathlib.Algebra.Order.Monoid.NatCast._hyg.371 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.NatCast._hyg.369 x._@.Mathlib.Algebra.Order.Monoid.NatCast._hyg.371)], LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) (OfNat.ofNat.{u1} α 0 (Zero.toOfNat0.{u1} α (AddMonoid.toZero.{u1} α (AddMonoidWithOne.toAddMonoid.{u1} α _inst_1)))) (OfNat.ofNat.{u1} α 4 (instOfNat.{u1} α 4 (AddMonoidWithOne.toNatCast.{u1} α _inst_1) (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))))
Case conversion may be inaccurate. Consider using '#align zero_le_four zero_le_fourₓ'. -/
theorem zero_le_four [Preorder α] [ZeroLEOneClass α] [CovariantClass α α (· + ·) (· ≤ ·)] :
    (0 : α) ≤ 4 :=
  add_nonneg zero_le_two zero_le_two
#align zero_le_four zero_le_four

/- warning: one_le_two -> one_le_two is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : AddMonoidWithOne.{u1} α] [_inst_2 : LE.{u1} α] [_inst_3 : ZeroLEOneClass.{u1} α (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddMonoidWithOne.toAddMonoid.{u1} α _inst_1))) (AddMonoidWithOne.toOne.{u1} α _inst_1) _inst_2] [_inst_4 : CovariantClass.{u1, u1} α α (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddMonoidWithOne.toAddMonoid.{u1} α _inst_1))))) (LE.le.{u1} α _inst_2)], LE.le.{u1} α _inst_2 (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (AddMonoidWithOne.toOne.{u1} α _inst_1)))) (OfNat.ofNat.{u1} α 2 (OfNat.mk.{u1} α 2 (bit0.{u1} α (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddMonoidWithOne.toAddMonoid.{u1} α _inst_1))) (One.one.{u1} α (AddMonoidWithOne.toOne.{u1} α _inst_1)))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : AddMonoidWithOne.{u1} α] [_inst_2 : LE.{u1} α] [_inst_3 : ZeroLEOneClass.{u1} α (AddMonoid.toZero.{u1} α (AddMonoidWithOne.toAddMonoid.{u1} α _inst_1)) (AddMonoidWithOne.toOne.{u1} α _inst_1) _inst_2] [_inst_4 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.NatCast._hyg.446 : α) (x._@.Mathlib.Algebra.Order.Monoid.NatCast._hyg.448 : α) => HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddMonoidWithOne.toAddMonoid.{u1} α _inst_1)))) x._@.Mathlib.Algebra.Order.Monoid.NatCast._hyg.446 x._@.Mathlib.Algebra.Order.Monoid.NatCast._hyg.448) (fun (x._@.Mathlib.Algebra.Order.Monoid.NatCast._hyg.461 : α) (x._@.Mathlib.Algebra.Order.Monoid.NatCast._hyg.463 : α) => LE.le.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Monoid.NatCast._hyg.461 x._@.Mathlib.Algebra.Order.Monoid.NatCast._hyg.463)], LE.le.{u1} α _inst_2 (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (AddMonoidWithOne.toOne.{u1} α _inst_1))) (OfNat.ofNat.{u1} α 2 (instOfNat.{u1} α 2 (AddMonoidWithOne.toNatCast.{u1} α _inst_1) (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)))))
Case conversion may be inaccurate. Consider using '#align one_le_two one_le_twoₓ'. -/
theorem one_le_two [LE α] [ZeroLEOneClass α] [CovariantClass α α (· + ·) (· ≤ ·)] : (1 : α) ≤ 2 :=
  calc
    1 = 1 + 0 := (add_zero 1).symm
    _ ≤ 1 + 1 := add_le_add_left zero_le_one _
    
#align one_le_two one_le_two

/- warning: one_le_two' -> one_le_two' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : AddMonoidWithOne.{u1} α] [_inst_2 : LE.{u1} α] [_inst_3 : ZeroLEOneClass.{u1} α (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddMonoidWithOne.toAddMonoid.{u1} α _inst_1))) (AddMonoidWithOne.toOne.{u1} α _inst_1) _inst_2] [_inst_4 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddMonoidWithOne.toAddMonoid.{u1} α _inst_1)))))) (LE.le.{u1} α _inst_2)], LE.le.{u1} α _inst_2 (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (AddMonoidWithOne.toOne.{u1} α _inst_1)))) (OfNat.ofNat.{u1} α 2 (OfNat.mk.{u1} α 2 (bit0.{u1} α (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddMonoidWithOne.toAddMonoid.{u1} α _inst_1))) (One.one.{u1} α (AddMonoidWithOne.toOne.{u1} α _inst_1)))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : AddMonoidWithOne.{u1} α] [_inst_2 : LE.{u1} α] [_inst_3 : ZeroLEOneClass.{u1} α (AddMonoid.toZero.{u1} α (AddMonoidWithOne.toAddMonoid.{u1} α _inst_1)) (AddMonoidWithOne.toOne.{u1} α _inst_1) _inst_2] [_inst_4 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.NatCast._hyg.538 : α) (x._@.Mathlib.Algebra.Order.Monoid.NatCast._hyg.540 : α) => HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddMonoidWithOne.toAddMonoid.{u1} α _inst_1)))) x._@.Mathlib.Algebra.Order.Monoid.NatCast._hyg.538 x._@.Mathlib.Algebra.Order.Monoid.NatCast._hyg.540)) (fun (x._@.Mathlib.Algebra.Order.Monoid.NatCast._hyg.553 : α) (x._@.Mathlib.Algebra.Order.Monoid.NatCast._hyg.555 : α) => LE.le.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Monoid.NatCast._hyg.553 x._@.Mathlib.Algebra.Order.Monoid.NatCast._hyg.555)], LE.le.{u1} α _inst_2 (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (AddMonoidWithOne.toOne.{u1} α _inst_1))) (OfNat.ofNat.{u1} α 2 (instOfNat.{u1} α 2 (AddMonoidWithOne.toNatCast.{u1} α _inst_1) (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)))))
Case conversion may be inaccurate. Consider using '#align one_le_two' one_le_two'ₓ'. -/
theorem one_le_two' [LE α] [ZeroLEOneClass α] [CovariantClass α α (swap (· + ·)) (· ≤ ·)] :
    (1 : α) ≤ 2 :=
  calc
    1 = 0 + 1 := (zero_add 1).symm
    _ ≤ 1 + 1 := add_le_add_right zero_le_one _
    
#align one_le_two' one_le_two'

section

variable [PartialOrder α] [ZeroLEOneClass α] [NeZero (1 : α)]

section

variable [CovariantClass α α (· + ·) (· ≤ ·)]

/- warning: zero_lt_two -> zero_lt_two is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : AddMonoidWithOne.{u1} α] [_inst_2 : PartialOrder.{u1} α] [_inst_3 : ZeroLEOneClass.{u1} α (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddMonoidWithOne.toAddMonoid.{u1} α _inst_1))) (AddMonoidWithOne.toOne.{u1} α _inst_1) (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2))] [_inst_4 : NeZero.{u1} α (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddMonoidWithOne.toAddMonoid.{u1} α _inst_1))) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (AddMonoidWithOne.toOne.{u1} α _inst_1))))] [_inst_5 : CovariantClass.{u1, u1} α α (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddMonoidWithOne.toAddMonoid.{u1} α _inst_1))))) (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)))], LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)) (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddMonoidWithOne.toAddMonoid.{u1} α _inst_1)))))) (OfNat.ofNat.{u1} α 2 (OfNat.mk.{u1} α 2 (bit0.{u1} α (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddMonoidWithOne.toAddMonoid.{u1} α _inst_1))) (One.one.{u1} α (AddMonoidWithOne.toOne.{u1} α _inst_1)))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : AddMonoidWithOne.{u1} α] [_inst_2 : PartialOrder.{u1} α] [_inst_3 : ZeroLEOneClass.{u1} α (AddMonoid.toZero.{u1} α (AddMonoidWithOne.toAddMonoid.{u1} α _inst_1)) (AddMonoidWithOne.toOne.{u1} α _inst_1) (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2))] [_inst_4 : NeZero.{u1} α (AddMonoid.toZero.{u1} α (AddMonoidWithOne.toAddMonoid.{u1} α _inst_1)) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (AddMonoidWithOne.toOne.{u1} α _inst_1)))] [_inst_5 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.NatCast._hyg.707 : α) (x._@.Mathlib.Algebra.Order.Monoid.NatCast._hyg.709 : α) => HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddMonoidWithOne.toAddMonoid.{u1} α _inst_1)))) x._@.Mathlib.Algebra.Order.Monoid.NatCast._hyg.707 x._@.Mathlib.Algebra.Order.Monoid.NatCast._hyg.709) (fun (x._@.Mathlib.Algebra.Order.Monoid.NatCast._hyg.722 : α) (x._@.Mathlib.Algebra.Order.Monoid.NatCast._hyg.724 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)) x._@.Mathlib.Algebra.Order.Monoid.NatCast._hyg.722 x._@.Mathlib.Algebra.Order.Monoid.NatCast._hyg.724)], LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)) (OfNat.ofNat.{u1} α 0 (Zero.toOfNat0.{u1} α (AddMonoid.toZero.{u1} α (AddMonoidWithOne.toAddMonoid.{u1} α _inst_1)))) (OfNat.ofNat.{u1} α 2 (instOfNat.{u1} α 2 (AddMonoidWithOne.toNatCast.{u1} α _inst_1) (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)))))
Case conversion may be inaccurate. Consider using '#align zero_lt_two zero_lt_twoₓ'. -/
/-- See `zero_lt_two'` for a version with the type explicit. -/
@[simp]
theorem zero_lt_two : (0 : α) < 2 :=
  zero_lt_one.trans_le one_le_two
#align zero_lt_two zero_lt_two

/- warning: zero_lt_three -> zero_lt_three is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : AddMonoidWithOne.{u1} α] [_inst_2 : PartialOrder.{u1} α] [_inst_3 : ZeroLEOneClass.{u1} α (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddMonoidWithOne.toAddMonoid.{u1} α _inst_1))) (AddMonoidWithOne.toOne.{u1} α _inst_1) (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2))] [_inst_4 : NeZero.{u1} α (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddMonoidWithOne.toAddMonoid.{u1} α _inst_1))) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (AddMonoidWithOne.toOne.{u1} α _inst_1))))] [_inst_5 : CovariantClass.{u1, u1} α α (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddMonoidWithOne.toAddMonoid.{u1} α _inst_1))))) (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)))], LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)) (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddMonoidWithOne.toAddMonoid.{u1} α _inst_1)))))) (OfNat.ofNat.{u1} α 3 (OfNat.mk.{u1} α 3 (bit1.{u1} α (AddMonoidWithOne.toOne.{u1} α _inst_1) (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddMonoidWithOne.toAddMonoid.{u1} α _inst_1))) (One.one.{u1} α (AddMonoidWithOne.toOne.{u1} α _inst_1)))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : AddMonoidWithOne.{u1} α] [_inst_2 : PartialOrder.{u1} α] [_inst_3 : ZeroLEOneClass.{u1} α (AddMonoid.toZero.{u1} α (AddMonoidWithOne.toAddMonoid.{u1} α _inst_1)) (AddMonoidWithOne.toOne.{u1} α _inst_1) (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2))] [_inst_4 : NeZero.{u1} α (AddMonoid.toZero.{u1} α (AddMonoidWithOne.toAddMonoid.{u1} α _inst_1)) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (AddMonoidWithOne.toOne.{u1} α _inst_1)))] [_inst_5 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.NatCast._hyg.771 : α) (x._@.Mathlib.Algebra.Order.Monoid.NatCast._hyg.773 : α) => HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddMonoidWithOne.toAddMonoid.{u1} α _inst_1)))) x._@.Mathlib.Algebra.Order.Monoid.NatCast._hyg.771 x._@.Mathlib.Algebra.Order.Monoid.NatCast._hyg.773) (fun (x._@.Mathlib.Algebra.Order.Monoid.NatCast._hyg.786 : α) (x._@.Mathlib.Algebra.Order.Monoid.NatCast._hyg.788 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)) x._@.Mathlib.Algebra.Order.Monoid.NatCast._hyg.786 x._@.Mathlib.Algebra.Order.Monoid.NatCast._hyg.788)], LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)) (OfNat.ofNat.{u1} α 0 (Zero.toOfNat0.{u1} α (AddMonoid.toZero.{u1} α (AddMonoidWithOne.toAddMonoid.{u1} α _inst_1)))) (OfNat.ofNat.{u1} α 3 (instOfNat.{u1} α 3 (AddMonoidWithOne.toNatCast.{u1} α _inst_1) (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))))
Case conversion may be inaccurate. Consider using '#align zero_lt_three zero_lt_threeₓ'. -/
/-- See `zero_lt_three'` for a version with the type explicit. -/
@[simp]
theorem zero_lt_three : (0 : α) < 3 :=
  lt_add_of_lt_of_nonneg zero_lt_two zero_le_one
#align zero_lt_three zero_lt_three

/- warning: zero_lt_four -> zero_lt_four is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : AddMonoidWithOne.{u1} α] [_inst_2 : PartialOrder.{u1} α] [_inst_3 : ZeroLEOneClass.{u1} α (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddMonoidWithOne.toAddMonoid.{u1} α _inst_1))) (AddMonoidWithOne.toOne.{u1} α _inst_1) (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2))] [_inst_4 : NeZero.{u1} α (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddMonoidWithOne.toAddMonoid.{u1} α _inst_1))) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (AddMonoidWithOne.toOne.{u1} α _inst_1))))] [_inst_5 : CovariantClass.{u1, u1} α α (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddMonoidWithOne.toAddMonoid.{u1} α _inst_1))))) (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)))], LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)) (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddMonoidWithOne.toAddMonoid.{u1} α _inst_1)))))) (OfNat.ofNat.{u1} α 4 (OfNat.mk.{u1} α 4 (bit0.{u1} α (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddMonoidWithOne.toAddMonoid.{u1} α _inst_1))) (bit0.{u1} α (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddMonoidWithOne.toAddMonoid.{u1} α _inst_1))) (One.one.{u1} α (AddMonoidWithOne.toOne.{u1} α _inst_1))))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : AddMonoidWithOne.{u1} α] [_inst_2 : PartialOrder.{u1} α] [_inst_3 : ZeroLEOneClass.{u1} α (AddMonoid.toZero.{u1} α (AddMonoidWithOne.toAddMonoid.{u1} α _inst_1)) (AddMonoidWithOne.toOne.{u1} α _inst_1) (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2))] [_inst_4 : NeZero.{u1} α (AddMonoid.toZero.{u1} α (AddMonoidWithOne.toAddMonoid.{u1} α _inst_1)) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (AddMonoidWithOne.toOne.{u1} α _inst_1)))] [_inst_5 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.NatCast._hyg.869 : α) (x._@.Mathlib.Algebra.Order.Monoid.NatCast._hyg.871 : α) => HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddMonoidWithOne.toAddMonoid.{u1} α _inst_1)))) x._@.Mathlib.Algebra.Order.Monoid.NatCast._hyg.869 x._@.Mathlib.Algebra.Order.Monoid.NatCast._hyg.871) (fun (x._@.Mathlib.Algebra.Order.Monoid.NatCast._hyg.884 : α) (x._@.Mathlib.Algebra.Order.Monoid.NatCast._hyg.886 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)) x._@.Mathlib.Algebra.Order.Monoid.NatCast._hyg.884 x._@.Mathlib.Algebra.Order.Monoid.NatCast._hyg.886)], LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)) (OfNat.ofNat.{u1} α 0 (Zero.toOfNat0.{u1} α (AddMonoid.toZero.{u1} α (AddMonoidWithOne.toAddMonoid.{u1} α _inst_1)))) (OfNat.ofNat.{u1} α 4 (instOfNat.{u1} α 4 (AddMonoidWithOne.toNatCast.{u1} α _inst_1) (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))))
Case conversion may be inaccurate. Consider using '#align zero_lt_four zero_lt_fourₓ'. -/
/-- See `zero_lt_four'` for a version with the type explicit. -/
@[simp]
theorem zero_lt_four : (0 : α) < 4 :=
  lt_add_of_lt_of_nonneg zero_lt_two zero_le_two
#align zero_lt_four zero_lt_four

variable (α)

/- warning: zero_lt_two' -> zero_lt_two' is a dubious translation:
lean 3 declaration is
  forall (α : Type.{u1}) [_inst_1 : AddMonoidWithOne.{u1} α] [_inst_2 : PartialOrder.{u1} α] [_inst_3 : ZeroLEOneClass.{u1} α (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddMonoidWithOne.toAddMonoid.{u1} α _inst_1))) (AddMonoidWithOne.toOne.{u1} α _inst_1) (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2))] [_inst_4 : NeZero.{u1} α (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddMonoidWithOne.toAddMonoid.{u1} α _inst_1))) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (AddMonoidWithOne.toOne.{u1} α _inst_1))))] [_inst_5 : CovariantClass.{u1, u1} α α (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddMonoidWithOne.toAddMonoid.{u1} α _inst_1))))) (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)))], LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)) (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddMonoidWithOne.toAddMonoid.{u1} α _inst_1)))))) (OfNat.ofNat.{u1} α 2 (OfNat.mk.{u1} α 2 (bit0.{u1} α (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddMonoidWithOne.toAddMonoid.{u1} α _inst_1))) (One.one.{u1} α (AddMonoidWithOne.toOne.{u1} α _inst_1)))))
but is expected to have type
  forall (α : Type.{u1}) [_inst_1 : AddMonoidWithOne.{u1} α] [_inst_2 : PartialOrder.{u1} α] [_inst_3 : ZeroLEOneClass.{u1} α (AddMonoid.toZero.{u1} α (AddMonoidWithOne.toAddMonoid.{u1} α _inst_1)) (AddMonoidWithOne.toOne.{u1} α _inst_1) (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2))] [_inst_4 : NeZero.{u1} α (AddMonoid.toZero.{u1} α (AddMonoidWithOne.toAddMonoid.{u1} α _inst_1)) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (AddMonoidWithOne.toOne.{u1} α _inst_1)))] [_inst_5 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.NatCast._hyg.1019 : α) (x._@.Mathlib.Algebra.Order.Monoid.NatCast._hyg.1021 : α) => HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddMonoidWithOne.toAddMonoid.{u1} α _inst_1)))) x._@.Mathlib.Algebra.Order.Monoid.NatCast._hyg.1019 x._@.Mathlib.Algebra.Order.Monoid.NatCast._hyg.1021) (fun (x._@.Mathlib.Algebra.Order.Monoid.NatCast._hyg.1034 : α) (x._@.Mathlib.Algebra.Order.Monoid.NatCast._hyg.1036 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)) x._@.Mathlib.Algebra.Order.Monoid.NatCast._hyg.1034 x._@.Mathlib.Algebra.Order.Monoid.NatCast._hyg.1036)], LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)) (OfNat.ofNat.{u1} α 0 (Zero.toOfNat0.{u1} α (AddMonoid.toZero.{u1} α (AddMonoidWithOne.toAddMonoid.{u1} α _inst_1)))) (OfNat.ofNat.{u1} α 2 (instOfNat.{u1} α 2 (AddMonoidWithOne.toNatCast.{u1} α _inst_1) (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)))))
Case conversion may be inaccurate. Consider using '#align zero_lt_two' zero_lt_two'ₓ'. -/
/-- See `zero_lt_two` for a version with the type implicit. -/
theorem zero_lt_two' : (0 : α) < 2 :=
  zero_lt_two
#align zero_lt_two' zero_lt_two'

/- warning: zero_lt_three' -> zero_lt_three' is a dubious translation:
lean 3 declaration is
  forall (α : Type.{u1}) [_inst_1 : AddMonoidWithOne.{u1} α] [_inst_2 : PartialOrder.{u1} α] [_inst_3 : ZeroLEOneClass.{u1} α (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddMonoidWithOne.toAddMonoid.{u1} α _inst_1))) (AddMonoidWithOne.toOne.{u1} α _inst_1) (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2))] [_inst_4 : NeZero.{u1} α (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddMonoidWithOne.toAddMonoid.{u1} α _inst_1))) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (AddMonoidWithOne.toOne.{u1} α _inst_1))))] [_inst_5 : CovariantClass.{u1, u1} α α (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddMonoidWithOne.toAddMonoid.{u1} α _inst_1))))) (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)))], LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)) (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddMonoidWithOne.toAddMonoid.{u1} α _inst_1)))))) (OfNat.ofNat.{u1} α 3 (OfNat.mk.{u1} α 3 (bit1.{u1} α (AddMonoidWithOne.toOne.{u1} α _inst_1) (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddMonoidWithOne.toAddMonoid.{u1} α _inst_1))) (One.one.{u1} α (AddMonoidWithOne.toOne.{u1} α _inst_1)))))
but is expected to have type
  forall (α : Type.{u1}) [_inst_1 : AddMonoidWithOne.{u1} α] [_inst_2 : PartialOrder.{u1} α] [_inst_3 : ZeroLEOneClass.{u1} α (AddMonoid.toZero.{u1} α (AddMonoidWithOne.toAddMonoid.{u1} α _inst_1)) (AddMonoidWithOne.toOne.{u1} α _inst_1) (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2))] [_inst_4 : NeZero.{u1} α (AddMonoid.toZero.{u1} α (AddMonoidWithOne.toAddMonoid.{u1} α _inst_1)) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (AddMonoidWithOne.toOne.{u1} α _inst_1)))] [_inst_5 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.NatCast._hyg.1082 : α) (x._@.Mathlib.Algebra.Order.Monoid.NatCast._hyg.1084 : α) => HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddMonoidWithOne.toAddMonoid.{u1} α _inst_1)))) x._@.Mathlib.Algebra.Order.Monoid.NatCast._hyg.1082 x._@.Mathlib.Algebra.Order.Monoid.NatCast._hyg.1084) (fun (x._@.Mathlib.Algebra.Order.Monoid.NatCast._hyg.1097 : α) (x._@.Mathlib.Algebra.Order.Monoid.NatCast._hyg.1099 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)) x._@.Mathlib.Algebra.Order.Monoid.NatCast._hyg.1097 x._@.Mathlib.Algebra.Order.Monoid.NatCast._hyg.1099)], LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)) (OfNat.ofNat.{u1} α 0 (Zero.toOfNat0.{u1} α (AddMonoid.toZero.{u1} α (AddMonoidWithOne.toAddMonoid.{u1} α _inst_1)))) (OfNat.ofNat.{u1} α 3 (instOfNat.{u1} α 3 (AddMonoidWithOne.toNatCast.{u1} α _inst_1) (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))))
Case conversion may be inaccurate. Consider using '#align zero_lt_three' zero_lt_three'ₓ'. -/
/-- See `zero_lt_three` for a version with the type implicit. -/
theorem zero_lt_three' : (0 : α) < 3 :=
  zero_lt_three
#align zero_lt_three' zero_lt_three'

/- warning: zero_lt_four' -> zero_lt_four' is a dubious translation:
lean 3 declaration is
  forall (α : Type.{u1}) [_inst_1 : AddMonoidWithOne.{u1} α] [_inst_2 : PartialOrder.{u1} α] [_inst_3 : ZeroLEOneClass.{u1} α (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddMonoidWithOne.toAddMonoid.{u1} α _inst_1))) (AddMonoidWithOne.toOne.{u1} α _inst_1) (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2))] [_inst_4 : NeZero.{u1} α (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddMonoidWithOne.toAddMonoid.{u1} α _inst_1))) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (AddMonoidWithOne.toOne.{u1} α _inst_1))))] [_inst_5 : CovariantClass.{u1, u1} α α (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddMonoidWithOne.toAddMonoid.{u1} α _inst_1))))) (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)))], LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)) (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddMonoidWithOne.toAddMonoid.{u1} α _inst_1)))))) (OfNat.ofNat.{u1} α 4 (OfNat.mk.{u1} α 4 (bit0.{u1} α (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddMonoidWithOne.toAddMonoid.{u1} α _inst_1))) (bit0.{u1} α (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddMonoidWithOne.toAddMonoid.{u1} α _inst_1))) (One.one.{u1} α (AddMonoidWithOne.toOne.{u1} α _inst_1))))))
but is expected to have type
  forall (α : Type.{u1}) [_inst_1 : AddMonoidWithOne.{u1} α] [_inst_2 : PartialOrder.{u1} α] [_inst_3 : ZeroLEOneClass.{u1} α (AddMonoid.toZero.{u1} α (AddMonoidWithOne.toAddMonoid.{u1} α _inst_1)) (AddMonoidWithOne.toOne.{u1} α _inst_1) (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2))] [_inst_4 : NeZero.{u1} α (AddMonoid.toZero.{u1} α (AddMonoidWithOne.toAddMonoid.{u1} α _inst_1)) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (AddMonoidWithOne.toOne.{u1} α _inst_1)))] [_inst_5 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.NatCast._hyg.1145 : α) (x._@.Mathlib.Algebra.Order.Monoid.NatCast._hyg.1147 : α) => HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddMonoidWithOne.toAddMonoid.{u1} α _inst_1)))) x._@.Mathlib.Algebra.Order.Monoid.NatCast._hyg.1145 x._@.Mathlib.Algebra.Order.Monoid.NatCast._hyg.1147) (fun (x._@.Mathlib.Algebra.Order.Monoid.NatCast._hyg.1160 : α) (x._@.Mathlib.Algebra.Order.Monoid.NatCast._hyg.1162 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)) x._@.Mathlib.Algebra.Order.Monoid.NatCast._hyg.1160 x._@.Mathlib.Algebra.Order.Monoid.NatCast._hyg.1162)], LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)) (OfNat.ofNat.{u1} α 0 (Zero.toOfNat0.{u1} α (AddMonoid.toZero.{u1} α (AddMonoidWithOne.toAddMonoid.{u1} α _inst_1)))) (OfNat.ofNat.{u1} α 4 (instOfNat.{u1} α 4 (AddMonoidWithOne.toNatCast.{u1} α _inst_1) (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))))
Case conversion may be inaccurate. Consider using '#align zero_lt_four' zero_lt_four'ₓ'. -/
/-- See `zero_lt_four` for a version with the type implicit. -/
theorem zero_lt_four' : (0 : α) < 4 :=
  zero_lt_four
#align zero_lt_four' zero_lt_four'

instance ZeroLEOneClass.NeZero.two : NeZero (2 : α) :=
  ⟨zero_lt_two.ne'⟩
#align zero_le_one_class.ne_zero.two ZeroLEOneClass.NeZero.two

instance ZeroLEOneClass.NeZero.three : NeZero (3 : α) :=
  ⟨zero_lt_three.ne'⟩
#align zero_le_one_class.ne_zero.three ZeroLEOneClass.NeZero.three

instance ZeroLEOneClass.NeZero.four : NeZero (4 : α) :=
  ⟨zero_lt_four.ne'⟩
#align zero_le_one_class.ne_zero.four ZeroLEOneClass.NeZero.four

end

/- warning: one_lt_two -> one_lt_two is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : AddMonoidWithOne.{u1} α] [_inst_2 : PartialOrder.{u1} α] [_inst_3 : ZeroLEOneClass.{u1} α (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddMonoidWithOne.toAddMonoid.{u1} α _inst_1))) (AddMonoidWithOne.toOne.{u1} α _inst_1) (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2))] [_inst_4 : NeZero.{u1} α (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddMonoidWithOne.toAddMonoid.{u1} α _inst_1))) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (AddMonoidWithOne.toOne.{u1} α _inst_1))))] [_inst_5 : CovariantClass.{u1, u1} α α (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddMonoidWithOne.toAddMonoid.{u1} α _inst_1))))) (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)))], LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (AddMonoidWithOne.toOne.{u1} α _inst_1)))) (OfNat.ofNat.{u1} α 2 (OfNat.mk.{u1} α 2 (bit0.{u1} α (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddMonoidWithOne.toAddMonoid.{u1} α _inst_1))) (One.one.{u1} α (AddMonoidWithOne.toOne.{u1} α _inst_1)))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : AddMonoidWithOne.{u1} α] [_inst_2 : PartialOrder.{u1} α] [_inst_3 : ZeroLEOneClass.{u1} α (AddMonoid.toZero.{u1} α (AddMonoidWithOne.toAddMonoid.{u1} α _inst_1)) (AddMonoidWithOne.toOne.{u1} α _inst_1) (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2))] [_inst_4 : NeZero.{u1} α (AddMonoid.toZero.{u1} α (AddMonoidWithOne.toAddMonoid.{u1} α _inst_1)) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (AddMonoidWithOne.toOne.{u1} α _inst_1)))] [_inst_5 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.NatCast._hyg.1398 : α) (x._@.Mathlib.Algebra.Order.Monoid.NatCast._hyg.1400 : α) => HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddMonoidWithOne.toAddMonoid.{u1} α _inst_1)))) x._@.Mathlib.Algebra.Order.Monoid.NatCast._hyg.1398 x._@.Mathlib.Algebra.Order.Monoid.NatCast._hyg.1400) (fun (x._@.Mathlib.Algebra.Order.Monoid.NatCast._hyg.1413 : α) (x._@.Mathlib.Algebra.Order.Monoid.NatCast._hyg.1415 : α) => LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)) x._@.Mathlib.Algebra.Order.Monoid.NatCast._hyg.1413 x._@.Mathlib.Algebra.Order.Monoid.NatCast._hyg.1415)], LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (AddMonoidWithOne.toOne.{u1} α _inst_1))) (OfNat.ofNat.{u1} α 2 (instOfNat.{u1} α 2 (AddMonoidWithOne.toNatCast.{u1} α _inst_1) (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)))))
Case conversion may be inaccurate. Consider using '#align one_lt_two one_lt_twoₓ'. -/
theorem one_lt_two [CovariantClass α α (· + ·) (· < ·)] : (1 : α) < 2 :=
  lt_add_one _
#align one_lt_two one_lt_two

end

alias zero_lt_two ← two_pos

alias zero_lt_three ← three_pos

alias zero_lt_four ← four_pos

