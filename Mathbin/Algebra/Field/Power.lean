/-
Copyright (c) 2014 Robert Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Lewis, Leonardo de Moura, Johannes Hölzl, Mario Carneiro

! This file was ported from Lean 3 source module algebra.field.power
! leanprover-community/mathlib commit 1126441d6bccf98c81214a0780c73d499f6721fe
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Field.Defs
import Mathbin.Algebra.GroupWithZero.Power
import Mathbin.Algebra.Parity

/-!
# Results about powers in fields or division rings.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file exists to ensure we can define `field` with minimal imports,
so contains some lemmas about powers of elements which need imports
beyond those needed for the basic definition.
-/


variable {α : Type _}

section DivisionRing

variable [DivisionRing α] {n : ℤ}

/- warning: zpow_bit1_neg -> zpow_bit1_neg is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DivisionRing.{u1} α] (a : α) (n : Int), Eq.{succ u1} α (HPow.hPow.{u1, 0, u1} α Int α (instHPow.{u1, 0} α Int (DivInvMonoid.Pow.{u1} α (DivisionRing.toDivInvMonoid.{u1} α _inst_1))) (Neg.neg.{u1} α (SubNegMonoid.toHasNeg.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddGroupWithOne.toAddGroup.{u1} α (NonAssocRing.toAddGroupWithOne.{u1} α (Ring.toNonAssocRing.{u1} α (DivisionRing.toRing.{u1} α _inst_1)))))) a) (bit1.{0} Int Int.hasOne Int.hasAdd n)) (Neg.neg.{u1} α (SubNegMonoid.toHasNeg.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddGroupWithOne.toAddGroup.{u1} α (NonAssocRing.toAddGroupWithOne.{u1} α (Ring.toNonAssocRing.{u1} α (DivisionRing.toRing.{u1} α _inst_1)))))) (HPow.hPow.{u1, 0, u1} α Int α (instHPow.{u1, 0} α Int (DivInvMonoid.Pow.{u1} α (DivisionRing.toDivInvMonoid.{u1} α _inst_1))) a (bit1.{0} Int Int.hasOne Int.hasAdd n)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DivisionRing.{u1} α] (a : α) (n : Int), Eq.{succ u1} α (HPow.hPow.{u1, 0, u1} α Int α (instHPow.{u1, 0} α Int (DivInvMonoid.Pow.{u1} α (DivisionRing.toDivInvMonoid.{u1} α _inst_1))) (Neg.neg.{u1} α (Ring.toNeg.{u1} α (DivisionRing.toRing.{u1} α _inst_1)) a) (bit1.{0} Int (NonAssocRing.toOne.{0} Int (Ring.toNonAssocRing.{0} Int Int.instRingInt)) Int.instAddInt n)) (Neg.neg.{u1} α (Ring.toNeg.{u1} α (DivisionRing.toRing.{u1} α _inst_1)) (HPow.hPow.{u1, 0, u1} α Int α (instHPow.{u1, 0} α Int (DivInvMonoid.Pow.{u1} α (DivisionRing.toDivInvMonoid.{u1} α _inst_1))) a (bit1.{0} Int (NonAssocRing.toOne.{0} Int (Ring.toNonAssocRing.{0} Int Int.instRingInt)) Int.instAddInt n)))
Case conversion may be inaccurate. Consider using '#align zpow_bit1_neg zpow_bit1_negₓ'. -/
@[simp]
theorem zpow_bit1_neg (a : α) (n : ℤ) : (-a) ^ bit1 n = -a ^ bit1 n := by
  rw [zpow_bit1', zpow_bit1', neg_mul_neg, neg_mul_eq_mul_neg]
#align zpow_bit1_neg zpow_bit1_neg

/- warning: odd.neg_zpow -> Odd.neg_zpow is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DivisionRing.{u1} α] {n : Int}, (Odd.{0} Int Int.semiring n) -> (forall (a : α), Eq.{succ u1} α (HPow.hPow.{u1, 0, u1} α Int α (instHPow.{u1, 0} α Int (DivInvMonoid.Pow.{u1} α (DivisionRing.toDivInvMonoid.{u1} α _inst_1))) (Neg.neg.{u1} α (SubNegMonoid.toHasNeg.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddGroupWithOne.toAddGroup.{u1} α (NonAssocRing.toAddGroupWithOne.{u1} α (Ring.toNonAssocRing.{u1} α (DivisionRing.toRing.{u1} α _inst_1)))))) a) n) (Neg.neg.{u1} α (SubNegMonoid.toHasNeg.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddGroupWithOne.toAddGroup.{u1} α (NonAssocRing.toAddGroupWithOne.{u1} α (Ring.toNonAssocRing.{u1} α (DivisionRing.toRing.{u1} α _inst_1)))))) (HPow.hPow.{u1, 0, u1} α Int α (instHPow.{u1, 0} α Int (DivInvMonoid.Pow.{u1} α (DivisionRing.toDivInvMonoid.{u1} α _inst_1))) a n)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DivisionRing.{u1} α] {n : Int}, (Odd.{0} Int Int.instSemiringInt n) -> (forall (a : α), Eq.{succ u1} α (HPow.hPow.{u1, 0, u1} α Int α (instHPow.{u1, 0} α Int (DivInvMonoid.Pow.{u1} α (DivisionRing.toDivInvMonoid.{u1} α _inst_1))) (Neg.neg.{u1} α (Ring.toNeg.{u1} α (DivisionRing.toRing.{u1} α _inst_1)) a) n) (Neg.neg.{u1} α (Ring.toNeg.{u1} α (DivisionRing.toRing.{u1} α _inst_1)) (HPow.hPow.{u1, 0, u1} α Int α (instHPow.{u1, 0} α Int (DivInvMonoid.Pow.{u1} α (DivisionRing.toDivInvMonoid.{u1} α _inst_1))) a n)))
Case conversion may be inaccurate. Consider using '#align odd.neg_zpow Odd.neg_zpowₓ'. -/
theorem Odd.neg_zpow (h : Odd n) (a : α) : (-a) ^ n = -a ^ n :=
  by
  obtain ⟨k, rfl⟩ := h.exists_bit1
  exact zpow_bit1_neg _ _
#align odd.neg_zpow Odd.neg_zpow

/- warning: odd.neg_one_zpow -> Odd.neg_one_zpow is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DivisionRing.{u1} α] {n : Int}, (Odd.{0} Int Int.semiring n) -> (Eq.{succ u1} α (HPow.hPow.{u1, 0, u1} α Int α (instHPow.{u1, 0} α Int (DivInvMonoid.Pow.{u1} α (DivisionRing.toDivInvMonoid.{u1} α _inst_1))) (Neg.neg.{u1} α (SubNegMonoid.toHasNeg.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddGroupWithOne.toAddGroup.{u1} α (NonAssocRing.toAddGroupWithOne.{u1} α (Ring.toNonAssocRing.{u1} α (DivisionRing.toRing.{u1} α _inst_1)))))) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (AddMonoidWithOne.toOne.{u1} α (AddGroupWithOne.toAddMonoidWithOne.{u1} α (NonAssocRing.toAddGroupWithOne.{u1} α (Ring.toNonAssocRing.{u1} α (DivisionRing.toRing.{u1} α _inst_1))))))))) n) (Neg.neg.{u1} α (SubNegMonoid.toHasNeg.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddGroupWithOne.toAddGroup.{u1} α (NonAssocRing.toAddGroupWithOne.{u1} α (Ring.toNonAssocRing.{u1} α (DivisionRing.toRing.{u1} α _inst_1)))))) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (AddMonoidWithOne.toOne.{u1} α (AddGroupWithOne.toAddMonoidWithOne.{u1} α (NonAssocRing.toAddGroupWithOne.{u1} α (Ring.toNonAssocRing.{u1} α (DivisionRing.toRing.{u1} α _inst_1))))))))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DivisionRing.{u1} α] {n : Int}, (Odd.{0} Int Int.instSemiringInt n) -> (Eq.{succ u1} α (HPow.hPow.{u1, 0, u1} α Int α (instHPow.{u1, 0} α Int (DivInvMonoid.Pow.{u1} α (DivisionRing.toDivInvMonoid.{u1} α _inst_1))) (Neg.neg.{u1} α (Ring.toNeg.{u1} α (DivisionRing.toRing.{u1} α _inst_1)) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (NonAssocRing.toOne.{u1} α (Ring.toNonAssocRing.{u1} α (DivisionRing.toRing.{u1} α _inst_1)))))) n) (Neg.neg.{u1} α (Ring.toNeg.{u1} α (DivisionRing.toRing.{u1} α _inst_1)) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (NonAssocRing.toOne.{u1} α (Ring.toNonAssocRing.{u1} α (DivisionRing.toRing.{u1} α _inst_1)))))))
Case conversion may be inaccurate. Consider using '#align odd.neg_one_zpow Odd.neg_one_zpowₓ'. -/
theorem Odd.neg_one_zpow (h : Odd n) : (-1 : α) ^ n = -1 := by rw [h.neg_zpow, one_zpow]
#align odd.neg_one_zpow Odd.neg_one_zpow

end DivisionRing

