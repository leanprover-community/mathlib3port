/-
Copyright (c) 2021 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Eric Rodriguez

! This file was ported from Lean 3 source module data.nat.choose.bounds
! leanprover-community/mathlib commit 6cb77a8eaff0ddd100e87b1591c6d3ad319514ff
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.GroupPower.Lemmas
import Mathbin.Algebra.Order.Field.Basic
import Mathbin.Data.Nat.Choose.Basic

/-!
# Inequalities for binomial coefficients

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file proves exponential bounds on binomial coefficients. We might want to add here the
bounds `n^r/r^r ≤ n.choose r ≤ e^r n^r/r^r` in the future.

## Main declarations

* `nat.choose_le_pow`: `n.choose r ≤ n^r / r!`
* `nat.pow_le_choose`: `(n + 1 - r)^r / r! ≤ n.choose r`. Beware of the fishy ℕ-subtraction.
-/


open Nat

variable {α : Type _} [LinearOrderedSemifield α]

namespace Nat

/- warning: nat.choose_le_pow -> Nat.choose_le_pow is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : LinearOrderedSemifield.{u1} α] (r : Nat) (n : Nat), LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCancelAddCommMonoid.toPartialOrder.{u1} α (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{u1} α (LinearOrderedSemiring.toStrictOrderedSemiring.{u1} α (LinearOrderedCommSemiring.toLinearOrderedSemiring.{u1} α (LinearOrderedSemifield.toLinearOrderedCommSemiring.{u1} α _inst_1))))))) ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Nat α (HasLiftT.mk.{1, succ u1} Nat α (CoeTCₓ.coe.{1, succ u1} Nat α (Nat.castCoe.{u1} α (AddMonoidWithOne.toNatCast.{u1} α (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} α (NonAssocSemiring.toAddCommMonoidWithOne.{u1} α (Semiring.toNonAssocSemiring.{u1} α (DivisionSemiring.toSemiring.{u1} α (Semifield.toDivisionSemiring.{u1} α (LinearOrderedSemifield.toSemifield.{u1} α _inst_1)))))))))) (Nat.choose n r)) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toHasDiv.{u1} α (GroupWithZero.toDivInvMonoid.{u1} α (DivisionSemiring.toGroupWithZero.{u1} α (Semifield.toDivisionSemiring.{u1} α (LinearOrderedSemifield.toSemifield.{u1} α _inst_1)))))) (HPow.hPow.{u1, 0, u1} α Nat α (instHPow.{u1, 0} α Nat (Monoid.Pow.{u1} α (MonoidWithZero.toMonoid.{u1} α (Semiring.toMonoidWithZero.{u1} α (DivisionSemiring.toSemiring.{u1} α (Semifield.toDivisionSemiring.{u1} α (LinearOrderedSemifield.toSemifield.{u1} α _inst_1))))))) ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Nat α (HasLiftT.mk.{1, succ u1} Nat α (CoeTCₓ.coe.{1, succ u1} Nat α (Nat.castCoe.{u1} α (AddMonoidWithOne.toNatCast.{u1} α (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} α (NonAssocSemiring.toAddCommMonoidWithOne.{u1} α (Semiring.toNonAssocSemiring.{u1} α (DivisionSemiring.toSemiring.{u1} α (Semifield.toDivisionSemiring.{u1} α (LinearOrderedSemifield.toSemifield.{u1} α _inst_1)))))))))) n) r) ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Nat α (HasLiftT.mk.{1, succ u1} Nat α (CoeTCₓ.coe.{1, succ u1} Nat α (Nat.castCoe.{u1} α (AddMonoidWithOne.toNatCast.{u1} α (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} α (NonAssocSemiring.toAddCommMonoidWithOne.{u1} α (Semiring.toNonAssocSemiring.{u1} α (DivisionSemiring.toSemiring.{u1} α (Semifield.toDivisionSemiring.{u1} α (LinearOrderedSemifield.toSemifield.{u1} α _inst_1)))))))))) (Nat.factorial r)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : LinearOrderedSemifield.{u1} α] (r : Nat) (n : Nat), LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (StrictOrderedSemiring.toPartialOrder.{u1} α (LinearOrderedSemiring.toStrictOrderedSemiring.{u1} α (LinearOrderedCommSemiring.toLinearOrderedSemiring.{u1} α (LinearOrderedSemifield.toLinearOrderedCommSemiring.{u1} α _inst_1)))))) (Nat.cast.{u1} α (Semiring.toNatCast.{u1} α (DivisionSemiring.toSemiring.{u1} α (Semifield.toDivisionSemiring.{u1} α (LinearOrderedSemifield.toSemifield.{u1} α _inst_1)))) (Nat.choose n r)) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (LinearOrderedSemifield.toDiv.{u1} α _inst_1)) (Nat.cast.{u1} α (Semiring.toNatCast.{u1} α (DivisionSemiring.toSemiring.{u1} α (Semifield.toDivisionSemiring.{u1} α (LinearOrderedSemifield.toSemifield.{u1} α _inst_1)))) (HPow.hPow.{0, 0, 0} Nat Nat Nat (instHPow.{0, 0} Nat Nat instPowNat) n r)) (Nat.cast.{u1} α (Semiring.toNatCast.{u1} α (DivisionSemiring.toSemiring.{u1} α (Semifield.toDivisionSemiring.{u1} α (LinearOrderedSemifield.toSemifield.{u1} α _inst_1)))) (Nat.factorial r)))
Case conversion may be inaccurate. Consider using '#align nat.choose_le_pow Nat.choose_le_powₓ'. -/
theorem choose_le_pow (r n : ℕ) : (n.choose r : α) ≤ n ^ r / r ! :=
  by
  rw [le_div_iff']
  · norm_cast
    rw [← Nat.descFactorial_eq_factorial_mul_choose]
    exact n.desc_factorial_le_pow r
  exact_mod_cast r.factorial_pos
#align nat.choose_le_pow Nat.choose_le_pow

/- warning: nat.pow_le_choose -> Nat.pow_le_choose is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : LinearOrderedSemifield.{u1} α] (r : Nat) (n : Nat), LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCancelAddCommMonoid.toPartialOrder.{u1} α (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{u1} α (LinearOrderedSemiring.toStrictOrderedSemiring.{u1} α (LinearOrderedCommSemiring.toLinearOrderedSemiring.{u1} α (LinearOrderedSemifield.toLinearOrderedCommSemiring.{u1} α _inst_1))))))) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toHasDiv.{u1} α (GroupWithZero.toDivInvMonoid.{u1} α (DivisionSemiring.toGroupWithZero.{u1} α (Semifield.toDivisionSemiring.{u1} α (LinearOrderedSemifield.toSemifield.{u1} α _inst_1)))))) (HPow.hPow.{u1, 0, u1} α Nat α (instHPow.{u1, 0} α Nat (Monoid.Pow.{u1} α (MonoidWithZero.toMonoid.{u1} α (Semiring.toMonoidWithZero.{u1} α (DivisionSemiring.toSemiring.{u1} α (Semifield.toDivisionSemiring.{u1} α (LinearOrderedSemifield.toSemifield.{u1} α _inst_1))))))) ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Nat α (HasLiftT.mk.{1, succ u1} Nat α (CoeTCₓ.coe.{1, succ u1} Nat α (Nat.castCoe.{u1} α (AddMonoidWithOne.toNatCast.{u1} α (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} α (NonAssocSemiring.toAddCommMonoidWithOne.{u1} α (Semiring.toNonAssocSemiring.{u1} α (DivisionSemiring.toSemiring.{u1} α (Semifield.toDivisionSemiring.{u1} α (LinearOrderedSemifield.toSemifield.{u1} α _inst_1)))))))))) (HSub.hSub.{0, 0, 0} Nat Nat Nat (instHSub.{0} Nat Nat.hasSub) (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))) r)) r) ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Nat α (HasLiftT.mk.{1, succ u1} Nat α (CoeTCₓ.coe.{1, succ u1} Nat α (Nat.castCoe.{u1} α (AddMonoidWithOne.toNatCast.{u1} α (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} α (NonAssocSemiring.toAddCommMonoidWithOne.{u1} α (Semiring.toNonAssocSemiring.{u1} α (DivisionSemiring.toSemiring.{u1} α (Semifield.toDivisionSemiring.{u1} α (LinearOrderedSemifield.toSemifield.{u1} α _inst_1)))))))))) (Nat.factorial r))) ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Nat α (HasLiftT.mk.{1, succ u1} Nat α (CoeTCₓ.coe.{1, succ u1} Nat α (Nat.castCoe.{u1} α (AddMonoidWithOne.toNatCast.{u1} α (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} α (NonAssocSemiring.toAddCommMonoidWithOne.{u1} α (Semiring.toNonAssocSemiring.{u1} α (DivisionSemiring.toSemiring.{u1} α (Semifield.toDivisionSemiring.{u1} α (LinearOrderedSemifield.toSemifield.{u1} α _inst_1)))))))))) (Nat.choose n r))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : LinearOrderedSemifield.{u1} α] (r : Nat) (n : Nat), LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (StrictOrderedSemiring.toPartialOrder.{u1} α (LinearOrderedSemiring.toStrictOrderedSemiring.{u1} α (LinearOrderedCommSemiring.toLinearOrderedSemiring.{u1} α (LinearOrderedSemifield.toLinearOrderedCommSemiring.{u1} α _inst_1)))))) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (LinearOrderedSemifield.toDiv.{u1} α _inst_1)) (Nat.cast.{u1} α (Semiring.toNatCast.{u1} α (DivisionSemiring.toSemiring.{u1} α (Semifield.toDivisionSemiring.{u1} α (LinearOrderedSemifield.toSemifield.{u1} α _inst_1)))) (HPow.hPow.{0, 0, 0} Nat Nat Nat (instHPow.{0, 0} Nat Nat instPowNat) (HSub.hSub.{0, 0, 0} Nat Nat Nat (instHSub.{0} Nat instSubNat) (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) r) r)) (Nat.cast.{u1} α (Semiring.toNatCast.{u1} α (DivisionSemiring.toSemiring.{u1} α (Semifield.toDivisionSemiring.{u1} α (LinearOrderedSemifield.toSemifield.{u1} α _inst_1)))) (Nat.factorial r))) (Nat.cast.{u1} α (Semiring.toNatCast.{u1} α (DivisionSemiring.toSemiring.{u1} α (Semifield.toDivisionSemiring.{u1} α (LinearOrderedSemifield.toSemifield.{u1} α _inst_1)))) (Nat.choose n r))
Case conversion may be inaccurate. Consider using '#align nat.pow_le_choose Nat.pow_le_chooseₓ'. -/
-- horrific casting is due to ℕ-subtraction
theorem pow_le_choose (r n : ℕ) : ((n + 1 - r : ℕ) ^ r : α) / r ! ≤ n.choose r :=
  by
  rw [div_le_iff']
  · norm_cast
    rw [← Nat.descFactorial_eq_factorial_mul_choose]
    exact n.pow_sub_le_desc_factorial r
  exact_mod_cast r.factorial_pos
#align nat.pow_le_choose Nat.pow_le_choose

end Nat

