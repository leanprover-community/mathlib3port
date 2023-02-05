/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin

! This file was ported from Lean 3 source module algebra.group_with_zero.power
! leanprover-community/mathlib commit 4c19a16e4b705bf135cf9a80ac18fcc99c438514
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.GroupPower.Lemmas
import Mathbin.Data.Int.Bitwise

/-!
# Powers of elements of groups with an adjoined zero element

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In this file we define integer power functions for groups with an adjoined zero element.
This generalises the integer power function on a division ring.
-/


section GroupWithZero

variable {G₀ : Type _} [GroupWithZero G₀] {a : G₀} {m n : ℕ}

section NatPow

/- warning: pow_sub₀ -> pow_sub₀ is a dubious translation:
lean 3 declaration is
  forall {G₀ : Type.{u1}} [_inst_1 : GroupWithZero.{u1} G₀] (a : G₀) {m : Nat} {n : Nat}, (Ne.{succ u1} G₀ a (OfNat.ofNat.{u1} G₀ 0 (OfNat.mk.{u1} G₀ 0 (Zero.zero.{u1} G₀ (MulZeroClass.toHasZero.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1)))))))) -> (LE.le.{0} Nat Nat.hasLe n m) -> (Eq.{succ u1} G₀ (HPow.hPow.{u1, 0, u1} G₀ Nat G₀ (instHPow.{u1, 0} G₀ Nat (Monoid.Pow.{u1} G₀ (MonoidWithZero.toMonoid.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1)))) a (HSub.hSub.{0, 0, 0} Nat Nat Nat (instHSub.{0} Nat Nat.hasSub) m n)) (HMul.hMul.{u1, u1, u1} G₀ G₀ G₀ (instHMul.{u1} G₀ (MulZeroClass.toHasMul.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1))))) (HPow.hPow.{u1, 0, u1} G₀ Nat G₀ (instHPow.{u1, 0} G₀ Nat (Monoid.Pow.{u1} G₀ (MonoidWithZero.toMonoid.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1)))) a m) (Inv.inv.{u1} G₀ (DivInvMonoid.toHasInv.{u1} G₀ (GroupWithZero.toDivInvMonoid.{u1} G₀ _inst_1)) (HPow.hPow.{u1, 0, u1} G₀ Nat G₀ (instHPow.{u1, 0} G₀ Nat (Monoid.Pow.{u1} G₀ (MonoidWithZero.toMonoid.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1)))) a n))))
but is expected to have type
  forall {G₀ : Type.{u1}} [_inst_1 : GroupWithZero.{u1} G₀] (a : G₀) {m : Nat} {n : Nat}, (Ne.{succ u1} G₀ a (OfNat.ofNat.{u1} G₀ 0 (Zero.toOfNat0.{u1} G₀ (MonoidWithZero.toZero.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1))))) -> (LE.le.{0} Nat instLENat n m) -> (Eq.{succ u1} G₀ (HPow.hPow.{u1, 0, u1} G₀ Nat G₀ (instHPow.{u1, 0} G₀ Nat (Monoid.Pow.{u1} G₀ (MonoidWithZero.toMonoid.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1)))) a (HSub.hSub.{0, 0, 0} Nat Nat Nat (instHSub.{0} Nat instSubNat) m n)) (HMul.hMul.{u1, u1, u1} G₀ G₀ G₀ (instHMul.{u1} G₀ (MulZeroClass.toMul.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1))))) (HPow.hPow.{u1, 0, u1} G₀ Nat G₀ (instHPow.{u1, 0} G₀ Nat (Monoid.Pow.{u1} G₀ (MonoidWithZero.toMonoid.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1)))) a m) (Inv.inv.{u1} G₀ (GroupWithZero.toInv.{u1} G₀ _inst_1) (HPow.hPow.{u1, 0, u1} G₀ Nat G₀ (instHPow.{u1, 0} G₀ Nat (Monoid.Pow.{u1} G₀ (MonoidWithZero.toMonoid.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1)))) a n))))
Case conversion may be inaccurate. Consider using '#align pow_sub₀ pow_sub₀ₓ'. -/
theorem pow_sub₀ (a : G₀) {m n : ℕ} (ha : a ≠ 0) (h : n ≤ m) : a ^ (m - n) = a ^ m * (a ^ n)⁻¹ :=
  by
  have h1 : m - n + n = m := tsub_add_cancel_of_le h
  have h2 : a ^ (m - n) * a ^ n = a ^ m := by rw [← pow_add, h1]
  simpa only [div_eq_mul_inv] using eq_div_of_mul_eq (pow_ne_zero _ ha) h2
#align pow_sub₀ pow_sub₀

/- warning: pow_sub_of_lt -> pow_sub_of_lt is a dubious translation:
lean 3 declaration is
  forall {G₀ : Type.{u1}} [_inst_1 : GroupWithZero.{u1} G₀] (a : G₀) {m : Nat} {n : Nat}, (LT.lt.{0} Nat Nat.hasLt n m) -> (Eq.{succ u1} G₀ (HPow.hPow.{u1, 0, u1} G₀ Nat G₀ (instHPow.{u1, 0} G₀ Nat (Monoid.Pow.{u1} G₀ (MonoidWithZero.toMonoid.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1)))) a (HSub.hSub.{0, 0, 0} Nat Nat Nat (instHSub.{0} Nat Nat.hasSub) m n)) (HMul.hMul.{u1, u1, u1} G₀ G₀ G₀ (instHMul.{u1} G₀ (MulZeroClass.toHasMul.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1))))) (HPow.hPow.{u1, 0, u1} G₀ Nat G₀ (instHPow.{u1, 0} G₀ Nat (Monoid.Pow.{u1} G₀ (MonoidWithZero.toMonoid.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1)))) a m) (Inv.inv.{u1} G₀ (DivInvMonoid.toHasInv.{u1} G₀ (GroupWithZero.toDivInvMonoid.{u1} G₀ _inst_1)) (HPow.hPow.{u1, 0, u1} G₀ Nat G₀ (instHPow.{u1, 0} G₀ Nat (Monoid.Pow.{u1} G₀ (MonoidWithZero.toMonoid.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1)))) a n))))
but is expected to have type
  forall {G₀ : Type.{u1}} [_inst_1 : GroupWithZero.{u1} G₀] (a : G₀) {m : Nat} {n : Nat}, (LT.lt.{0} Nat instLTNat n m) -> (Eq.{succ u1} G₀ (HPow.hPow.{u1, 0, u1} G₀ Nat G₀ (instHPow.{u1, 0} G₀ Nat (Monoid.Pow.{u1} G₀ (MonoidWithZero.toMonoid.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1)))) a (HSub.hSub.{0, 0, 0} Nat Nat Nat (instHSub.{0} Nat instSubNat) m n)) (HMul.hMul.{u1, u1, u1} G₀ G₀ G₀ (instHMul.{u1} G₀ (MulZeroClass.toMul.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1))))) (HPow.hPow.{u1, 0, u1} G₀ Nat G₀ (instHPow.{u1, 0} G₀ Nat (Monoid.Pow.{u1} G₀ (MonoidWithZero.toMonoid.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1)))) a m) (Inv.inv.{u1} G₀ (GroupWithZero.toInv.{u1} G₀ _inst_1) (HPow.hPow.{u1, 0, u1} G₀ Nat G₀ (instHPow.{u1, 0} G₀ Nat (Monoid.Pow.{u1} G₀ (MonoidWithZero.toMonoid.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1)))) a n))))
Case conversion may be inaccurate. Consider using '#align pow_sub_of_lt pow_sub_of_ltₓ'. -/
theorem pow_sub_of_lt (a : G₀) {m n : ℕ} (h : n < m) : a ^ (m - n) = a ^ m * (a ^ n)⁻¹ :=
  by
  obtain rfl | ha := eq_or_ne a 0
  · rw [zero_pow (tsub_pos_of_lt h), zero_pow (n.zero_le.trans_lt h), zero_mul]
  · exact pow_sub₀ _ ha h.le
#align pow_sub_of_lt pow_sub_of_lt

/- warning: pow_inv_comm₀ -> pow_inv_comm₀ is a dubious translation:
lean 3 declaration is
  forall {G₀ : Type.{u1}} [_inst_1 : GroupWithZero.{u1} G₀] (a : G₀) (m : Nat) (n : Nat), Eq.{succ u1} G₀ (HMul.hMul.{u1, u1, u1} G₀ G₀ G₀ (instHMul.{u1} G₀ (MulZeroClass.toHasMul.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1))))) (HPow.hPow.{u1, 0, u1} G₀ Nat G₀ (instHPow.{u1, 0} G₀ Nat (Monoid.Pow.{u1} G₀ (MonoidWithZero.toMonoid.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1)))) (Inv.inv.{u1} G₀ (DivInvMonoid.toHasInv.{u1} G₀ (GroupWithZero.toDivInvMonoid.{u1} G₀ _inst_1)) a) m) (HPow.hPow.{u1, 0, u1} G₀ Nat G₀ (instHPow.{u1, 0} G₀ Nat (Monoid.Pow.{u1} G₀ (MonoidWithZero.toMonoid.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1)))) a n)) (HMul.hMul.{u1, u1, u1} G₀ G₀ G₀ (instHMul.{u1} G₀ (MulZeroClass.toHasMul.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1))))) (HPow.hPow.{u1, 0, u1} G₀ Nat G₀ (instHPow.{u1, 0} G₀ Nat (Monoid.Pow.{u1} G₀ (MonoidWithZero.toMonoid.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1)))) a n) (HPow.hPow.{u1, 0, u1} G₀ Nat G₀ (instHPow.{u1, 0} G₀ Nat (Monoid.Pow.{u1} G₀ (MonoidWithZero.toMonoid.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1)))) (Inv.inv.{u1} G₀ (DivInvMonoid.toHasInv.{u1} G₀ (GroupWithZero.toDivInvMonoid.{u1} G₀ _inst_1)) a) m))
but is expected to have type
  forall {G₀ : Type.{u1}} [_inst_1 : GroupWithZero.{u1} G₀] (a : G₀) (m : Nat) (n : Nat), Eq.{succ u1} G₀ (HMul.hMul.{u1, u1, u1} G₀ G₀ G₀ (instHMul.{u1} G₀ (MulZeroClass.toMul.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1))))) (HPow.hPow.{u1, 0, u1} G₀ Nat G₀ (instHPow.{u1, 0} G₀ Nat (Monoid.Pow.{u1} G₀ (MonoidWithZero.toMonoid.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1)))) (Inv.inv.{u1} G₀ (GroupWithZero.toInv.{u1} G₀ _inst_1) a) m) (HPow.hPow.{u1, 0, u1} G₀ Nat G₀ (instHPow.{u1, 0} G₀ Nat (Monoid.Pow.{u1} G₀ (MonoidWithZero.toMonoid.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1)))) a n)) (HMul.hMul.{u1, u1, u1} G₀ G₀ G₀ (instHMul.{u1} G₀ (MulZeroClass.toMul.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1))))) (HPow.hPow.{u1, 0, u1} G₀ Nat G₀ (instHPow.{u1, 0} G₀ Nat (Monoid.Pow.{u1} G₀ (MonoidWithZero.toMonoid.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1)))) a n) (HPow.hPow.{u1, 0, u1} G₀ Nat G₀ (instHPow.{u1, 0} G₀ Nat (Monoid.Pow.{u1} G₀ (MonoidWithZero.toMonoid.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1)))) (Inv.inv.{u1} G₀ (GroupWithZero.toInv.{u1} G₀ _inst_1) a) m))
Case conversion may be inaccurate. Consider using '#align pow_inv_comm₀ pow_inv_comm₀ₓ'. -/
theorem pow_inv_comm₀ (a : G₀) (m n : ℕ) : a⁻¹ ^ m * a ^ n = a ^ n * a⁻¹ ^ m :=
  (Commute.refl a).inv_left₀.pow_powₓ m n
#align pow_inv_comm₀ pow_inv_comm₀

/- warning: inv_pow_sub₀ -> inv_pow_sub₀ is a dubious translation:
lean 3 declaration is
  forall {G₀ : Type.{u1}} [_inst_1 : GroupWithZero.{u1} G₀] {a : G₀} {m : Nat} {n : Nat}, (Ne.{succ u1} G₀ a (OfNat.ofNat.{u1} G₀ 0 (OfNat.mk.{u1} G₀ 0 (Zero.zero.{u1} G₀ (MulZeroClass.toHasZero.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1)))))))) -> (LE.le.{0} Nat Nat.hasLe n m) -> (Eq.{succ u1} G₀ (HPow.hPow.{u1, 0, u1} G₀ Nat G₀ (instHPow.{u1, 0} G₀ Nat (Monoid.Pow.{u1} G₀ (MonoidWithZero.toMonoid.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1)))) (Inv.inv.{u1} G₀ (DivInvMonoid.toHasInv.{u1} G₀ (GroupWithZero.toDivInvMonoid.{u1} G₀ _inst_1)) a) (HSub.hSub.{0, 0, 0} Nat Nat Nat (instHSub.{0} Nat Nat.hasSub) m n)) (HMul.hMul.{u1, u1, u1} G₀ G₀ G₀ (instHMul.{u1} G₀ (MulZeroClass.toHasMul.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1))))) (Inv.inv.{u1} G₀ (DivInvMonoid.toHasInv.{u1} G₀ (GroupWithZero.toDivInvMonoid.{u1} G₀ _inst_1)) (HPow.hPow.{u1, 0, u1} G₀ Nat G₀ (instHPow.{u1, 0} G₀ Nat (Monoid.Pow.{u1} G₀ (MonoidWithZero.toMonoid.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1)))) a m)) (HPow.hPow.{u1, 0, u1} G₀ Nat G₀ (instHPow.{u1, 0} G₀ Nat (Monoid.Pow.{u1} G₀ (MonoidWithZero.toMonoid.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1)))) a n)))
but is expected to have type
  forall {G₀ : Type.{u1}} [_inst_1 : GroupWithZero.{u1} G₀] {a : G₀} {m : Nat} {n : Nat}, (Ne.{succ u1} G₀ a (OfNat.ofNat.{u1} G₀ 0 (Zero.toOfNat0.{u1} G₀ (MonoidWithZero.toZero.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1))))) -> (LE.le.{0} Nat instLENat n m) -> (Eq.{succ u1} G₀ (HPow.hPow.{u1, 0, u1} G₀ Nat G₀ (instHPow.{u1, 0} G₀ Nat (Monoid.Pow.{u1} G₀ (MonoidWithZero.toMonoid.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1)))) (Inv.inv.{u1} G₀ (GroupWithZero.toInv.{u1} G₀ _inst_1) a) (HSub.hSub.{0, 0, 0} Nat Nat Nat (instHSub.{0} Nat instSubNat) m n)) (HMul.hMul.{u1, u1, u1} G₀ G₀ G₀ (instHMul.{u1} G₀ (MulZeroClass.toMul.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1))))) (Inv.inv.{u1} G₀ (GroupWithZero.toInv.{u1} G₀ _inst_1) (HPow.hPow.{u1, 0, u1} G₀ Nat G₀ (instHPow.{u1, 0} G₀ Nat (Monoid.Pow.{u1} G₀ (MonoidWithZero.toMonoid.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1)))) a m)) (HPow.hPow.{u1, 0, u1} G₀ Nat G₀ (instHPow.{u1, 0} G₀ Nat (Monoid.Pow.{u1} G₀ (MonoidWithZero.toMonoid.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1)))) a n)))
Case conversion may be inaccurate. Consider using '#align inv_pow_sub₀ inv_pow_sub₀ₓ'. -/
theorem inv_pow_sub₀ (ha : a ≠ 0) (h : n ≤ m) : a⁻¹ ^ (m - n) = (a ^ m)⁻¹ * a ^ n := by
  rw [pow_sub₀ _ (inv_ne_zero ha) h, inv_pow, inv_pow, inv_inv]
#align inv_pow_sub₀ inv_pow_sub₀

/- warning: inv_pow_sub_of_lt -> inv_pow_sub_of_lt is a dubious translation:
lean 3 declaration is
  forall {G₀ : Type.{u1}} [_inst_1 : GroupWithZero.{u1} G₀] {m : Nat} {n : Nat} (a : G₀), (LT.lt.{0} Nat Nat.hasLt n m) -> (Eq.{succ u1} G₀ (HPow.hPow.{u1, 0, u1} G₀ Nat G₀ (instHPow.{u1, 0} G₀ Nat (Monoid.Pow.{u1} G₀ (MonoidWithZero.toMonoid.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1)))) (Inv.inv.{u1} G₀ (DivInvMonoid.toHasInv.{u1} G₀ (GroupWithZero.toDivInvMonoid.{u1} G₀ _inst_1)) a) (HSub.hSub.{0, 0, 0} Nat Nat Nat (instHSub.{0} Nat Nat.hasSub) m n)) (HMul.hMul.{u1, u1, u1} G₀ G₀ G₀ (instHMul.{u1} G₀ (MulZeroClass.toHasMul.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1))))) (Inv.inv.{u1} G₀ (DivInvMonoid.toHasInv.{u1} G₀ (GroupWithZero.toDivInvMonoid.{u1} G₀ _inst_1)) (HPow.hPow.{u1, 0, u1} G₀ Nat G₀ (instHPow.{u1, 0} G₀ Nat (Monoid.Pow.{u1} G₀ (MonoidWithZero.toMonoid.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1)))) a m)) (HPow.hPow.{u1, 0, u1} G₀ Nat G₀ (instHPow.{u1, 0} G₀ Nat (Monoid.Pow.{u1} G₀ (MonoidWithZero.toMonoid.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1)))) a n)))
but is expected to have type
  forall {G₀ : Type.{u1}} [_inst_1 : GroupWithZero.{u1} G₀] {m : Nat} {n : Nat} (a : G₀), (LT.lt.{0} Nat instLTNat n m) -> (Eq.{succ u1} G₀ (HPow.hPow.{u1, 0, u1} G₀ Nat G₀ (instHPow.{u1, 0} G₀ Nat (Monoid.Pow.{u1} G₀ (MonoidWithZero.toMonoid.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1)))) (Inv.inv.{u1} G₀ (GroupWithZero.toInv.{u1} G₀ _inst_1) a) (HSub.hSub.{0, 0, 0} Nat Nat Nat (instHSub.{0} Nat instSubNat) m n)) (HMul.hMul.{u1, u1, u1} G₀ G₀ G₀ (instHMul.{u1} G₀ (MulZeroClass.toMul.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1))))) (Inv.inv.{u1} G₀ (GroupWithZero.toInv.{u1} G₀ _inst_1) (HPow.hPow.{u1, 0, u1} G₀ Nat G₀ (instHPow.{u1, 0} G₀ Nat (Monoid.Pow.{u1} G₀ (MonoidWithZero.toMonoid.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1)))) a m)) (HPow.hPow.{u1, 0, u1} G₀ Nat G₀ (instHPow.{u1, 0} G₀ Nat (Monoid.Pow.{u1} G₀ (MonoidWithZero.toMonoid.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1)))) a n)))
Case conversion may be inaccurate. Consider using '#align inv_pow_sub_of_lt inv_pow_sub_of_ltₓ'. -/
theorem inv_pow_sub_of_lt (a : G₀) (h : n < m) : a⁻¹ ^ (m - n) = (a ^ m)⁻¹ * a ^ n := by
  rw [pow_sub_of_lt a⁻¹ h, inv_pow, inv_pow, inv_inv]
#align inv_pow_sub_of_lt inv_pow_sub_of_lt

end NatPow

end GroupWithZero

section Zpow

open Int

variable {G₀ : Type _} [GroupWithZero G₀]

attribute [local ematch] le_of_lt

/- warning: zero_zpow -> zero_zpow is a dubious translation:
lean 3 declaration is
  forall {G₀ : Type.{u1}} [_inst_1 : GroupWithZero.{u1} G₀] (z : Int), (Ne.{1} Int z (OfNat.ofNat.{0} Int 0 (OfNat.mk.{0} Int 0 (Zero.zero.{0} Int Int.hasZero)))) -> (Eq.{succ u1} G₀ (HPow.hPow.{u1, 0, u1} G₀ Int G₀ (instHPow.{u1, 0} G₀ Int (DivInvMonoid.Pow.{u1} G₀ (GroupWithZero.toDivInvMonoid.{u1} G₀ _inst_1))) (OfNat.ofNat.{u1} G₀ 0 (OfNat.mk.{u1} G₀ 0 (Zero.zero.{u1} G₀ (MulZeroClass.toHasZero.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1))))))) z) (OfNat.ofNat.{u1} G₀ 0 (OfNat.mk.{u1} G₀ 0 (Zero.zero.{u1} G₀ (MulZeroClass.toHasZero.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1))))))))
but is expected to have type
  forall {G₀ : Type.{u1}} [_inst_1 : GroupWithZero.{u1} G₀] (z : Int), (Ne.{1} Int z (OfNat.ofNat.{0} Int 0 (instOfNatInt 0))) -> (Eq.{succ u1} G₀ (HPow.hPow.{u1, 0, u1} G₀ Int G₀ (instHPow.{u1, 0} G₀ Int (DivInvMonoid.Pow.{u1} G₀ (GroupWithZero.toDivInvMonoid.{u1} G₀ _inst_1))) (OfNat.ofNat.{u1} G₀ 0 (Zero.toOfNat0.{u1} G₀ (MonoidWithZero.toZero.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1)))) z) (OfNat.ofNat.{u1} G₀ 0 (Zero.toOfNat0.{u1} G₀ (MonoidWithZero.toZero.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1)))))
Case conversion may be inaccurate. Consider using '#align zero_zpow zero_zpowₓ'. -/
theorem zero_zpow : ∀ z : ℤ, z ≠ 0 → (0 : G₀) ^ z = 0
  | (n : ℕ), h => by
    rw [zpow_ofNat, zero_pow']
    simpa using h
  | -[n+1], h => by simp
#align zero_zpow zero_zpow

/- warning: zero_zpow_eq -> zero_zpow_eq is a dubious translation:
lean 3 declaration is
  forall {G₀ : Type.{u1}} [_inst_1 : GroupWithZero.{u1} G₀] (n : Int), Eq.{succ u1} G₀ (HPow.hPow.{u1, 0, u1} G₀ Int G₀ (instHPow.{u1, 0} G₀ Int (DivInvMonoid.Pow.{u1} G₀ (GroupWithZero.toDivInvMonoid.{u1} G₀ _inst_1))) (OfNat.ofNat.{u1} G₀ 0 (OfNat.mk.{u1} G₀ 0 (Zero.zero.{u1} G₀ (MulZeroClass.toHasZero.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1))))))) n) (ite.{succ u1} G₀ (Eq.{1} Int n (OfNat.ofNat.{0} Int 0 (OfNat.mk.{0} Int 0 (Zero.zero.{0} Int Int.hasZero)))) (Int.decidableEq n (OfNat.ofNat.{0} Int 0 (OfNat.mk.{0} Int 0 (Zero.zero.{0} Int Int.hasZero)))) (OfNat.ofNat.{u1} G₀ 1 (OfNat.mk.{u1} G₀ 1 (One.one.{u1} G₀ (MulOneClass.toHasOne.{u1} G₀ (MulZeroOneClass.toMulOneClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1))))))) (OfNat.ofNat.{u1} G₀ 0 (OfNat.mk.{u1} G₀ 0 (Zero.zero.{u1} G₀ (MulZeroClass.toHasZero.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1))))))))
but is expected to have type
  forall {G₀ : Type.{u1}} [_inst_1 : GroupWithZero.{u1} G₀] (n : Int), Eq.{succ u1} G₀ (HPow.hPow.{u1, 0, u1} G₀ Int G₀ (instHPow.{u1, 0} G₀ Int (DivInvMonoid.Pow.{u1} G₀ (GroupWithZero.toDivInvMonoid.{u1} G₀ _inst_1))) (OfNat.ofNat.{u1} G₀ 0 (Zero.toOfNat0.{u1} G₀ (MonoidWithZero.toZero.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1)))) n) (ite.{succ u1} G₀ (Eq.{1} Int n (OfNat.ofNat.{0} Int 0 (instOfNatInt 0))) (Int.instDecidableEqInt n (OfNat.ofNat.{0} Int 0 (instOfNatInt 0))) (OfNat.ofNat.{u1} G₀ 1 (One.toOfNat1.{u1} G₀ (InvOneClass.toOne.{u1} G₀ (DivInvOneMonoid.toInvOneClass.{u1} G₀ (DivisionMonoid.toDivInvOneMonoid.{u1} G₀ (GroupWithZero.toDivisionMonoid.{u1} G₀ _inst_1)))))) (OfNat.ofNat.{u1} G₀ 0 (Zero.toOfNat0.{u1} G₀ (MonoidWithZero.toZero.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1)))))
Case conversion may be inaccurate. Consider using '#align zero_zpow_eq zero_zpow_eqₓ'. -/
theorem zero_zpow_eq (n : ℤ) : (0 : G₀) ^ n = if n = 0 then 1 else 0 :=
  by
  split_ifs with h
  · rw [h, zpow_zero]
  · rw [zero_zpow _ h]
#align zero_zpow_eq zero_zpow_eq

/- warning: zpow_add_one₀ -> zpow_add_one₀ is a dubious translation:
lean 3 declaration is
  forall {G₀ : Type.{u1}} [_inst_1 : GroupWithZero.{u1} G₀] {a : G₀}, (Ne.{succ u1} G₀ a (OfNat.ofNat.{u1} G₀ 0 (OfNat.mk.{u1} G₀ 0 (Zero.zero.{u1} G₀ (MulZeroClass.toHasZero.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1)))))))) -> (forall (n : Int), Eq.{succ u1} G₀ (HPow.hPow.{u1, 0, u1} G₀ Int G₀ (instHPow.{u1, 0} G₀ Int (DivInvMonoid.Pow.{u1} G₀ (GroupWithZero.toDivInvMonoid.{u1} G₀ _inst_1))) a (HAdd.hAdd.{0, 0, 0} Int Int Int (instHAdd.{0} Int Int.hasAdd) n (OfNat.ofNat.{0} Int 1 (OfNat.mk.{0} Int 1 (One.one.{0} Int Int.hasOne))))) (HMul.hMul.{u1, u1, u1} G₀ G₀ G₀ (instHMul.{u1} G₀ (MulZeroClass.toHasMul.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1))))) (HPow.hPow.{u1, 0, u1} G₀ Int G₀ (instHPow.{u1, 0} G₀ Int (DivInvMonoid.Pow.{u1} G₀ (GroupWithZero.toDivInvMonoid.{u1} G₀ _inst_1))) a n) a))
but is expected to have type
  forall {G₀ : Type.{u1}} [_inst_1 : GroupWithZero.{u1} G₀] {a : G₀}, (Ne.{succ u1} G₀ a (OfNat.ofNat.{u1} G₀ 0 (Zero.toOfNat0.{u1} G₀ (MonoidWithZero.toZero.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1))))) -> (forall (n : Int), Eq.{succ u1} G₀ (HPow.hPow.{u1, 0, u1} G₀ Int G₀ (instHPow.{u1, 0} G₀ Int (DivInvMonoid.Pow.{u1} G₀ (GroupWithZero.toDivInvMonoid.{u1} G₀ _inst_1))) a (HAdd.hAdd.{0, 0, 0} Int Int Int (instHAdd.{0} Int Int.instAddInt) n (OfNat.ofNat.{0} Int 1 (instOfNatInt 1)))) (HMul.hMul.{u1, u1, u1} G₀ G₀ G₀ (instHMul.{u1} G₀ (MulZeroClass.toMul.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1))))) (HPow.hPow.{u1, 0, u1} G₀ Int G₀ (instHPow.{u1, 0} G₀ Int (DivInvMonoid.Pow.{u1} G₀ (GroupWithZero.toDivInvMonoid.{u1} G₀ _inst_1))) a n) a))
Case conversion may be inaccurate. Consider using '#align zpow_add_one₀ zpow_add_one₀ₓ'. -/
theorem zpow_add_one₀ {a : G₀} (ha : a ≠ 0) : ∀ n : ℤ, a ^ (n + 1) = a ^ n * a
  | (n : ℕ) => by simp only [← Int.ofNat_succ, zpow_ofNat, pow_succ']
  | -[0+1] => by erw [zpow_zero, zpow_negSucc, pow_one, inv_mul_cancel ha]
  | -[n + 1+1] => by
    rw [Int.negSucc_eq, zpow_neg, neg_add, neg_add_cancel_right, zpow_neg, ← Int.ofNat_succ,
      zpow_ofNat, zpow_ofNat, pow_succ _ (n + 1), mul_inv_rev, mul_assoc, inv_mul_cancel ha,
      mul_one]
#align zpow_add_one₀ zpow_add_one₀

/- warning: zpow_sub_one₀ -> zpow_sub_one₀ is a dubious translation:
lean 3 declaration is
  forall {G₀ : Type.{u1}} [_inst_1 : GroupWithZero.{u1} G₀] {a : G₀}, (Ne.{succ u1} G₀ a (OfNat.ofNat.{u1} G₀ 0 (OfNat.mk.{u1} G₀ 0 (Zero.zero.{u1} G₀ (MulZeroClass.toHasZero.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1)))))))) -> (forall (n : Int), Eq.{succ u1} G₀ (HPow.hPow.{u1, 0, u1} G₀ Int G₀ (instHPow.{u1, 0} G₀ Int (DivInvMonoid.Pow.{u1} G₀ (GroupWithZero.toDivInvMonoid.{u1} G₀ _inst_1))) a (HSub.hSub.{0, 0, 0} Int Int Int (instHSub.{0} Int Int.hasSub) n (OfNat.ofNat.{0} Int 1 (OfNat.mk.{0} Int 1 (One.one.{0} Int Int.hasOne))))) (HMul.hMul.{u1, u1, u1} G₀ G₀ G₀ (instHMul.{u1} G₀ (MulZeroClass.toHasMul.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1))))) (HPow.hPow.{u1, 0, u1} G₀ Int G₀ (instHPow.{u1, 0} G₀ Int (DivInvMonoid.Pow.{u1} G₀ (GroupWithZero.toDivInvMonoid.{u1} G₀ _inst_1))) a n) (Inv.inv.{u1} G₀ (DivInvMonoid.toHasInv.{u1} G₀ (GroupWithZero.toDivInvMonoid.{u1} G₀ _inst_1)) a)))
but is expected to have type
  forall {G₀ : Type.{u1}} [_inst_1 : GroupWithZero.{u1} G₀] {a : G₀}, (Ne.{succ u1} G₀ a (OfNat.ofNat.{u1} G₀ 0 (Zero.toOfNat0.{u1} G₀ (MonoidWithZero.toZero.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1))))) -> (forall (n : Int), Eq.{succ u1} G₀ (HPow.hPow.{u1, 0, u1} G₀ Int G₀ (instHPow.{u1, 0} G₀ Int (DivInvMonoid.Pow.{u1} G₀ (GroupWithZero.toDivInvMonoid.{u1} G₀ _inst_1))) a (HSub.hSub.{0, 0, 0} Int Int Int (instHSub.{0} Int Int.instSubInt) n (OfNat.ofNat.{0} Int 1 (instOfNatInt 1)))) (HMul.hMul.{u1, u1, u1} G₀ G₀ G₀ (instHMul.{u1} G₀ (MulZeroClass.toMul.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1))))) (HPow.hPow.{u1, 0, u1} G₀ Int G₀ (instHPow.{u1, 0} G₀ Int (DivInvMonoid.Pow.{u1} G₀ (GroupWithZero.toDivInvMonoid.{u1} G₀ _inst_1))) a n) (Inv.inv.{u1} G₀ (GroupWithZero.toInv.{u1} G₀ _inst_1) a)))
Case conversion may be inaccurate. Consider using '#align zpow_sub_one₀ zpow_sub_one₀ₓ'. -/
theorem zpow_sub_one₀ {a : G₀} (ha : a ≠ 0) (n : ℤ) : a ^ (n - 1) = a ^ n * a⁻¹ :=
  calc
    a ^ (n - 1) = a ^ (n - 1) * a * a⁻¹ := by rw [mul_assoc, mul_inv_cancel ha, mul_one]
    _ = a ^ n * a⁻¹ := by rw [← zpow_add_one₀ ha, sub_add_cancel]
    
#align zpow_sub_one₀ zpow_sub_one₀

/- warning: zpow_add₀ -> zpow_add₀ is a dubious translation:
lean 3 declaration is
  forall {G₀ : Type.{u1}} [_inst_1 : GroupWithZero.{u1} G₀] {a : G₀}, (Ne.{succ u1} G₀ a (OfNat.ofNat.{u1} G₀ 0 (OfNat.mk.{u1} G₀ 0 (Zero.zero.{u1} G₀ (MulZeroClass.toHasZero.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1)))))))) -> (forall (m : Int) (n : Int), Eq.{succ u1} G₀ (HPow.hPow.{u1, 0, u1} G₀ Int G₀ (instHPow.{u1, 0} G₀ Int (DivInvMonoid.Pow.{u1} G₀ (GroupWithZero.toDivInvMonoid.{u1} G₀ _inst_1))) a (HAdd.hAdd.{0, 0, 0} Int Int Int (instHAdd.{0} Int Int.hasAdd) m n)) (HMul.hMul.{u1, u1, u1} G₀ G₀ G₀ (instHMul.{u1} G₀ (MulZeroClass.toHasMul.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1))))) (HPow.hPow.{u1, 0, u1} G₀ Int G₀ (instHPow.{u1, 0} G₀ Int (DivInvMonoid.Pow.{u1} G₀ (GroupWithZero.toDivInvMonoid.{u1} G₀ _inst_1))) a m) (HPow.hPow.{u1, 0, u1} G₀ Int G₀ (instHPow.{u1, 0} G₀ Int (DivInvMonoid.Pow.{u1} G₀ (GroupWithZero.toDivInvMonoid.{u1} G₀ _inst_1))) a n)))
but is expected to have type
  forall {G₀ : Type.{u1}} [_inst_1 : GroupWithZero.{u1} G₀] {a : G₀}, (Ne.{succ u1} G₀ a (OfNat.ofNat.{u1} G₀ 0 (Zero.toOfNat0.{u1} G₀ (MonoidWithZero.toZero.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1))))) -> (forall (m : Int) (n : Int), Eq.{succ u1} G₀ (HPow.hPow.{u1, 0, u1} G₀ Int G₀ (instHPow.{u1, 0} G₀ Int (DivInvMonoid.Pow.{u1} G₀ (GroupWithZero.toDivInvMonoid.{u1} G₀ _inst_1))) a (HAdd.hAdd.{0, 0, 0} Int Int Int (instHAdd.{0} Int Int.instAddInt) m n)) (HMul.hMul.{u1, u1, u1} G₀ G₀ G₀ (instHMul.{u1} G₀ (MulZeroClass.toMul.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1))))) (HPow.hPow.{u1, 0, u1} G₀ Int G₀ (instHPow.{u1, 0} G₀ Int (DivInvMonoid.Pow.{u1} G₀ (GroupWithZero.toDivInvMonoid.{u1} G₀ _inst_1))) a m) (HPow.hPow.{u1, 0, u1} G₀ Int G₀ (instHPow.{u1, 0} G₀ Int (DivInvMonoid.Pow.{u1} G₀ (GroupWithZero.toDivInvMonoid.{u1} G₀ _inst_1))) a n)))
Case conversion may be inaccurate. Consider using '#align zpow_add₀ zpow_add₀ₓ'. -/
theorem zpow_add₀ {a : G₀} (ha : a ≠ 0) (m n : ℤ) : a ^ (m + n) = a ^ m * a ^ n :=
  by
  induction' n using Int.induction_on with n ihn n ihn
  case hz => simp
  · simp only [← add_assoc, zpow_add_one₀ ha, ihn, mul_assoc]
  · rw [zpow_sub_one₀ ha, ← mul_assoc, ← ihn, ← zpow_sub_one₀ ha, add_sub_assoc]
#align zpow_add₀ zpow_add₀

/- warning: zpow_add' -> zpow_add' is a dubious translation:
lean 3 declaration is
  forall {G₀ : Type.{u1}} [_inst_1 : GroupWithZero.{u1} G₀] {a : G₀} {m : Int} {n : Int}, (Or (Ne.{succ u1} G₀ a (OfNat.ofNat.{u1} G₀ 0 (OfNat.mk.{u1} G₀ 0 (Zero.zero.{u1} G₀ (MulZeroClass.toHasZero.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1)))))))) (Or (Ne.{1} Int (HAdd.hAdd.{0, 0, 0} Int Int Int (instHAdd.{0} Int Int.hasAdd) m n) (OfNat.ofNat.{0} Int 0 (OfNat.mk.{0} Int 0 (Zero.zero.{0} Int Int.hasZero)))) (And (Eq.{1} Int m (OfNat.ofNat.{0} Int 0 (OfNat.mk.{0} Int 0 (Zero.zero.{0} Int Int.hasZero)))) (Eq.{1} Int n (OfNat.ofNat.{0} Int 0 (OfNat.mk.{0} Int 0 (Zero.zero.{0} Int Int.hasZero))))))) -> (Eq.{succ u1} G₀ (HPow.hPow.{u1, 0, u1} G₀ Int G₀ (instHPow.{u1, 0} G₀ Int (DivInvMonoid.Pow.{u1} G₀ (GroupWithZero.toDivInvMonoid.{u1} G₀ _inst_1))) a (HAdd.hAdd.{0, 0, 0} Int Int Int (instHAdd.{0} Int Int.hasAdd) m n)) (HMul.hMul.{u1, u1, u1} G₀ G₀ G₀ (instHMul.{u1} G₀ (MulZeroClass.toHasMul.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1))))) (HPow.hPow.{u1, 0, u1} G₀ Int G₀ (instHPow.{u1, 0} G₀ Int (DivInvMonoid.Pow.{u1} G₀ (GroupWithZero.toDivInvMonoid.{u1} G₀ _inst_1))) a m) (HPow.hPow.{u1, 0, u1} G₀ Int G₀ (instHPow.{u1, 0} G₀ Int (DivInvMonoid.Pow.{u1} G₀ (GroupWithZero.toDivInvMonoid.{u1} G₀ _inst_1))) a n)))
but is expected to have type
  forall {G₀ : Type.{u1}} [_inst_1 : GroupWithZero.{u1} G₀] {a : G₀} {m : Int} {n : Int}, (Or (Ne.{succ u1} G₀ a (OfNat.ofNat.{u1} G₀ 0 (Zero.toOfNat0.{u1} G₀ (MonoidWithZero.toZero.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1))))) (Or (Ne.{1} Int (HAdd.hAdd.{0, 0, 0} Int Int Int (instHAdd.{0} Int Int.instAddInt) m n) (OfNat.ofNat.{0} Int 0 (instOfNatInt 0))) (And (Eq.{1} Int m (OfNat.ofNat.{0} Int 0 (instOfNatInt 0))) (Eq.{1} Int n (OfNat.ofNat.{0} Int 0 (instOfNatInt 0)))))) -> (Eq.{succ u1} G₀ (HPow.hPow.{u1, 0, u1} G₀ Int G₀ (instHPow.{u1, 0} G₀ Int (DivInvMonoid.Pow.{u1} G₀ (GroupWithZero.toDivInvMonoid.{u1} G₀ _inst_1))) a (HAdd.hAdd.{0, 0, 0} Int Int Int (instHAdd.{0} Int Int.instAddInt) m n)) (HMul.hMul.{u1, u1, u1} G₀ G₀ G₀ (instHMul.{u1} G₀ (MulZeroClass.toMul.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1))))) (HPow.hPow.{u1, 0, u1} G₀ Int G₀ (instHPow.{u1, 0} G₀ Int (DivInvMonoid.Pow.{u1} G₀ (GroupWithZero.toDivInvMonoid.{u1} G₀ _inst_1))) a m) (HPow.hPow.{u1, 0, u1} G₀ Int G₀ (instHPow.{u1, 0} G₀ Int (DivInvMonoid.Pow.{u1} G₀ (GroupWithZero.toDivInvMonoid.{u1} G₀ _inst_1))) a n)))
Case conversion may be inaccurate. Consider using '#align zpow_add' zpow_add'ₓ'. -/
theorem zpow_add' {a : G₀} {m n : ℤ} (h : a ≠ 0 ∨ m + n ≠ 0 ∨ m = 0 ∧ n = 0) :
    a ^ (m + n) = a ^ m * a ^ n := by
  by_cases hm : m = 0; · simp [hm]
  by_cases hn : n = 0; · simp [hn]
  by_cases ha : a = 0
  · subst a
    simp only [false_or_iff, eq_self_iff_true, not_true, Ne.def, hm, hn, false_and_iff,
      or_false_iff] at h
    rw [zero_zpow _ h, zero_zpow _ hm, zero_mul]
  · exact zpow_add₀ ha m n
#align zpow_add' zpow_add'

/- warning: zpow_one_add₀ -> zpow_one_add₀ is a dubious translation:
lean 3 declaration is
  forall {G₀ : Type.{u1}} [_inst_1 : GroupWithZero.{u1} G₀] {a : G₀}, (Ne.{succ u1} G₀ a (OfNat.ofNat.{u1} G₀ 0 (OfNat.mk.{u1} G₀ 0 (Zero.zero.{u1} G₀ (MulZeroClass.toHasZero.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1)))))))) -> (forall (i : Int), Eq.{succ u1} G₀ (HPow.hPow.{u1, 0, u1} G₀ Int G₀ (instHPow.{u1, 0} G₀ Int (DivInvMonoid.Pow.{u1} G₀ (GroupWithZero.toDivInvMonoid.{u1} G₀ _inst_1))) a (HAdd.hAdd.{0, 0, 0} Int Int Int (instHAdd.{0} Int Int.hasAdd) (OfNat.ofNat.{0} Int 1 (OfNat.mk.{0} Int 1 (One.one.{0} Int Int.hasOne))) i)) (HMul.hMul.{u1, u1, u1} G₀ G₀ G₀ (instHMul.{u1} G₀ (MulZeroClass.toHasMul.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1))))) a (HPow.hPow.{u1, 0, u1} G₀ Int G₀ (instHPow.{u1, 0} G₀ Int (DivInvMonoid.Pow.{u1} G₀ (GroupWithZero.toDivInvMonoid.{u1} G₀ _inst_1))) a i)))
but is expected to have type
  forall {G₀ : Type.{u1}} [_inst_1 : GroupWithZero.{u1} G₀] {a : G₀}, (Ne.{succ u1} G₀ a (OfNat.ofNat.{u1} G₀ 0 (Zero.toOfNat0.{u1} G₀ (MonoidWithZero.toZero.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1))))) -> (forall (i : Int), Eq.{succ u1} G₀ (HPow.hPow.{u1, 0, u1} G₀ Int G₀ (instHPow.{u1, 0} G₀ Int (DivInvMonoid.Pow.{u1} G₀ (GroupWithZero.toDivInvMonoid.{u1} G₀ _inst_1))) a (HAdd.hAdd.{0, 0, 0} Int Int Int (instHAdd.{0} Int Int.instAddInt) (OfNat.ofNat.{0} Int 1 (instOfNatInt 1)) i)) (HMul.hMul.{u1, u1, u1} G₀ G₀ G₀ (instHMul.{u1} G₀ (MulZeroClass.toMul.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1))))) a (HPow.hPow.{u1, 0, u1} G₀ Int G₀ (instHPow.{u1, 0} G₀ Int (DivInvMonoid.Pow.{u1} G₀ (GroupWithZero.toDivInvMonoid.{u1} G₀ _inst_1))) a i)))
Case conversion may be inaccurate. Consider using '#align zpow_one_add₀ zpow_one_add₀ₓ'. -/
theorem zpow_one_add₀ {a : G₀} (h : a ≠ 0) (i : ℤ) : a ^ (1 + i) = a * a ^ i := by
  rw [zpow_add₀ h, zpow_one]
#align zpow_one_add₀ zpow_one_add₀

/- warning: semiconj_by.zpow_right₀ -> SemiconjBy.zpow_right₀ is a dubious translation:
lean 3 declaration is
  forall {G₀ : Type.{u1}} [_inst_1 : GroupWithZero.{u1} G₀] {a : G₀} {x : G₀} {y : G₀}, (SemiconjBy.{u1} G₀ (MulZeroClass.toHasMul.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1)))) a x y) -> (forall (m : Int), SemiconjBy.{u1} G₀ (MulZeroClass.toHasMul.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1)))) a (HPow.hPow.{u1, 0, u1} G₀ Int G₀ (instHPow.{u1, 0} G₀ Int (DivInvMonoid.Pow.{u1} G₀ (GroupWithZero.toDivInvMonoid.{u1} G₀ _inst_1))) x m) (HPow.hPow.{u1, 0, u1} G₀ Int G₀ (instHPow.{u1, 0} G₀ Int (DivInvMonoid.Pow.{u1} G₀ (GroupWithZero.toDivInvMonoid.{u1} G₀ _inst_1))) y m))
but is expected to have type
  forall {G₀ : Type.{u1}} [_inst_1 : GroupWithZero.{u1} G₀] {a : G₀} {x : G₀} {y : G₀}, (SemiconjBy.{u1} G₀ (MulZeroClass.toMul.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1)))) a x y) -> (forall (m : Int), SemiconjBy.{u1} G₀ (MulZeroClass.toMul.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1)))) a (HPow.hPow.{u1, 0, u1} G₀ Int G₀ (instHPow.{u1, 0} G₀ Int (DivInvMonoid.Pow.{u1} G₀ (GroupWithZero.toDivInvMonoid.{u1} G₀ _inst_1))) x m) (HPow.hPow.{u1, 0, u1} G₀ Int G₀ (instHPow.{u1, 0} G₀ Int (DivInvMonoid.Pow.{u1} G₀ (GroupWithZero.toDivInvMonoid.{u1} G₀ _inst_1))) y m))
Case conversion may be inaccurate. Consider using '#align semiconj_by.zpow_right₀ SemiconjBy.zpow_right₀ₓ'. -/
theorem SemiconjBy.zpow_right₀ {a x y : G₀} (h : SemiconjBy a x y) :
    ∀ m : ℤ, SemiconjBy a (x ^ m) (y ^ m)
  | (n : ℕ) => by simp [h.pow_right n]
  | -[n+1] => by simp [(h.pow_right (n + 1)).inv_right₀]
#align semiconj_by.zpow_right₀ SemiconjBy.zpow_right₀

/- warning: commute.zpow_right₀ -> Commute.zpow_right₀ is a dubious translation:
lean 3 declaration is
  forall {G₀ : Type.{u1}} [_inst_1 : GroupWithZero.{u1} G₀] {a : G₀} {b : G₀}, (Commute.{u1} G₀ (MulZeroClass.toHasMul.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1)))) a b) -> (forall (m : Int), Commute.{u1} G₀ (MulZeroClass.toHasMul.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1)))) a (HPow.hPow.{u1, 0, u1} G₀ Int G₀ (instHPow.{u1, 0} G₀ Int (DivInvMonoid.Pow.{u1} G₀ (GroupWithZero.toDivInvMonoid.{u1} G₀ _inst_1))) b m))
but is expected to have type
  forall {G₀ : Type.{u1}} [_inst_1 : GroupWithZero.{u1} G₀] {a : G₀} {b : G₀}, (Commute.{u1} G₀ (MulZeroClass.toMul.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1)))) a b) -> (forall (m : Int), Commute.{u1} G₀ (MulZeroClass.toMul.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1)))) a (HPow.hPow.{u1, 0, u1} G₀ Int G₀ (instHPow.{u1, 0} G₀ Int (DivInvMonoid.Pow.{u1} G₀ (GroupWithZero.toDivInvMonoid.{u1} G₀ _inst_1))) b m))
Case conversion may be inaccurate. Consider using '#align commute.zpow_right₀ Commute.zpow_right₀ₓ'. -/
theorem Commute.zpow_right₀ {a b : G₀} (h : Commute a b) : ∀ m : ℤ, Commute a (b ^ m) :=
  h.zpow_right₀
#align commute.zpow_right₀ Commute.zpow_right₀

/- warning: commute.zpow_left₀ -> Commute.zpow_left₀ is a dubious translation:
lean 3 declaration is
  forall {G₀ : Type.{u1}} [_inst_1 : GroupWithZero.{u1} G₀] {a : G₀} {b : G₀}, (Commute.{u1} G₀ (MulZeroClass.toHasMul.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1)))) a b) -> (forall (m : Int), Commute.{u1} G₀ (MulZeroClass.toHasMul.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1)))) (HPow.hPow.{u1, 0, u1} G₀ Int G₀ (instHPow.{u1, 0} G₀ Int (DivInvMonoid.Pow.{u1} G₀ (GroupWithZero.toDivInvMonoid.{u1} G₀ _inst_1))) a m) b)
but is expected to have type
  forall {G₀ : Type.{u1}} [_inst_1 : GroupWithZero.{u1} G₀] {a : G₀} {b : G₀}, (Commute.{u1} G₀ (MulZeroClass.toMul.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1)))) a b) -> (forall (m : Int), Commute.{u1} G₀ (MulZeroClass.toMul.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1)))) (HPow.hPow.{u1, 0, u1} G₀ Int G₀ (instHPow.{u1, 0} G₀ Int (DivInvMonoid.Pow.{u1} G₀ (GroupWithZero.toDivInvMonoid.{u1} G₀ _inst_1))) a m) b)
Case conversion may be inaccurate. Consider using '#align commute.zpow_left₀ Commute.zpow_left₀ₓ'. -/
theorem Commute.zpow_left₀ {a b : G₀} (h : Commute a b) (m : ℤ) : Commute (a ^ m) b :=
  (h.symm.zpow_right₀ m).symm
#align commute.zpow_left₀ Commute.zpow_left₀

/- warning: commute.zpow_zpow₀ -> Commute.zpow_zpow₀ is a dubious translation:
lean 3 declaration is
  forall {G₀ : Type.{u1}} [_inst_1 : GroupWithZero.{u1} G₀] {a : G₀} {b : G₀}, (Commute.{u1} G₀ (MulZeroClass.toHasMul.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1)))) a b) -> (forall (m : Int) (n : Int), Commute.{u1} G₀ (MulZeroClass.toHasMul.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1)))) (HPow.hPow.{u1, 0, u1} G₀ Int G₀ (instHPow.{u1, 0} G₀ Int (DivInvMonoid.Pow.{u1} G₀ (GroupWithZero.toDivInvMonoid.{u1} G₀ _inst_1))) a m) (HPow.hPow.{u1, 0, u1} G₀ Int G₀ (instHPow.{u1, 0} G₀ Int (DivInvMonoid.Pow.{u1} G₀ (GroupWithZero.toDivInvMonoid.{u1} G₀ _inst_1))) b n))
but is expected to have type
  forall {G₀ : Type.{u1}} [_inst_1 : GroupWithZero.{u1} G₀] {a : G₀} {b : G₀}, (Commute.{u1} G₀ (MulZeroClass.toMul.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1)))) a b) -> (forall (m : Int) (n : Int), Commute.{u1} G₀ (MulZeroClass.toMul.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1)))) (HPow.hPow.{u1, 0, u1} G₀ Int G₀ (instHPow.{u1, 0} G₀ Int (DivInvMonoid.Pow.{u1} G₀ (GroupWithZero.toDivInvMonoid.{u1} G₀ _inst_1))) a m) (HPow.hPow.{u1, 0, u1} G₀ Int G₀ (instHPow.{u1, 0} G₀ Int (DivInvMonoid.Pow.{u1} G₀ (GroupWithZero.toDivInvMonoid.{u1} G₀ _inst_1))) b n))
Case conversion may be inaccurate. Consider using '#align commute.zpow_zpow₀ Commute.zpow_zpow₀ₓ'. -/
theorem Commute.zpow_zpow₀ {a b : G₀} (h : Commute a b) (m n : ℤ) : Commute (a ^ m) (b ^ n) :=
  (h.zpow_left₀ m).zpow_right₀ n
#align commute.zpow_zpow₀ Commute.zpow_zpow₀

/- warning: commute.zpow_self₀ -> Commute.zpow_self₀ is a dubious translation:
lean 3 declaration is
  forall {G₀ : Type.{u1}} [_inst_1 : GroupWithZero.{u1} G₀] (a : G₀) (n : Int), Commute.{u1} G₀ (MulZeroClass.toHasMul.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1)))) (HPow.hPow.{u1, 0, u1} G₀ Int G₀ (instHPow.{u1, 0} G₀ Int (DivInvMonoid.Pow.{u1} G₀ (GroupWithZero.toDivInvMonoid.{u1} G₀ _inst_1))) a n) a
but is expected to have type
  forall {G₀ : Type.{u1}} [_inst_1 : GroupWithZero.{u1} G₀] (a : G₀) (n : Int), Commute.{u1} G₀ (MulZeroClass.toMul.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1)))) (HPow.hPow.{u1, 0, u1} G₀ Int G₀ (instHPow.{u1, 0} G₀ Int (DivInvMonoid.Pow.{u1} G₀ (GroupWithZero.toDivInvMonoid.{u1} G₀ _inst_1))) a n) a
Case conversion may be inaccurate. Consider using '#align commute.zpow_self₀ Commute.zpow_self₀ₓ'. -/
theorem Commute.zpow_self₀ (a : G₀) (n : ℤ) : Commute (a ^ n) a :=
  (Commute.refl a).zpow_left₀ n
#align commute.zpow_self₀ Commute.zpow_self₀

/- warning: commute.self_zpow₀ -> Commute.self_zpow₀ is a dubious translation:
lean 3 declaration is
  forall {G₀ : Type.{u1}} [_inst_1 : GroupWithZero.{u1} G₀] (a : G₀) (n : Int), Commute.{u1} G₀ (MulZeroClass.toHasMul.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1)))) a (HPow.hPow.{u1, 0, u1} G₀ Int G₀ (instHPow.{u1, 0} G₀ Int (DivInvMonoid.Pow.{u1} G₀ (GroupWithZero.toDivInvMonoid.{u1} G₀ _inst_1))) a n)
but is expected to have type
  forall {G₀ : Type.{u1}} [_inst_1 : GroupWithZero.{u1} G₀] (a : G₀) (n : Int), Commute.{u1} G₀ (MulZeroClass.toMul.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1)))) a (HPow.hPow.{u1, 0, u1} G₀ Int G₀ (instHPow.{u1, 0} G₀ Int (DivInvMonoid.Pow.{u1} G₀ (GroupWithZero.toDivInvMonoid.{u1} G₀ _inst_1))) a n)
Case conversion may be inaccurate. Consider using '#align commute.self_zpow₀ Commute.self_zpow₀ₓ'. -/
theorem Commute.self_zpow₀ (a : G₀) (n : ℤ) : Commute a (a ^ n) :=
  (Commute.refl a).zpow_right₀ n
#align commute.self_zpow₀ Commute.self_zpow₀

/- warning: commute.zpow_zpow_self₀ -> Commute.zpow_zpow_self₀ is a dubious translation:
lean 3 declaration is
  forall {G₀ : Type.{u1}} [_inst_1 : GroupWithZero.{u1} G₀] (a : G₀) (m : Int) (n : Int), Commute.{u1} G₀ (MulZeroClass.toHasMul.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1)))) (HPow.hPow.{u1, 0, u1} G₀ Int G₀ (instHPow.{u1, 0} G₀ Int (DivInvMonoid.Pow.{u1} G₀ (GroupWithZero.toDivInvMonoid.{u1} G₀ _inst_1))) a m) (HPow.hPow.{u1, 0, u1} G₀ Int G₀ (instHPow.{u1, 0} G₀ Int (DivInvMonoid.Pow.{u1} G₀ (GroupWithZero.toDivInvMonoid.{u1} G₀ _inst_1))) a n)
but is expected to have type
  forall {G₀ : Type.{u1}} [_inst_1 : GroupWithZero.{u1} G₀] (a : G₀) (m : Int) (n : Int), Commute.{u1} G₀ (MulZeroClass.toMul.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1)))) (HPow.hPow.{u1, 0, u1} G₀ Int G₀ (instHPow.{u1, 0} G₀ Int (DivInvMonoid.Pow.{u1} G₀ (GroupWithZero.toDivInvMonoid.{u1} G₀ _inst_1))) a m) (HPow.hPow.{u1, 0, u1} G₀ Int G₀ (instHPow.{u1, 0} G₀ Int (DivInvMonoid.Pow.{u1} G₀ (GroupWithZero.toDivInvMonoid.{u1} G₀ _inst_1))) a n)
Case conversion may be inaccurate. Consider using '#align commute.zpow_zpow_self₀ Commute.zpow_zpow_self₀ₓ'. -/
theorem Commute.zpow_zpow_self₀ (a : G₀) (m n : ℤ) : Commute (a ^ m) (a ^ n) :=
  (Commute.refl a).zpow_zpow₀ m n
#align commute.zpow_zpow_self₀ Commute.zpow_zpow_self₀

/- warning: zpow_bit1₀ -> zpow_bit1₀ is a dubious translation:
lean 3 declaration is
  forall {G₀ : Type.{u1}} [_inst_1 : GroupWithZero.{u1} G₀] (a : G₀) (n : Int), Eq.{succ u1} G₀ (HPow.hPow.{u1, 0, u1} G₀ Int G₀ (instHPow.{u1, 0} G₀ Int (DivInvMonoid.Pow.{u1} G₀ (GroupWithZero.toDivInvMonoid.{u1} G₀ _inst_1))) a (bit1.{0} Int Int.hasOne Int.hasAdd n)) (HMul.hMul.{u1, u1, u1} G₀ G₀ G₀ (instHMul.{u1} G₀ (MulZeroClass.toHasMul.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1))))) (HMul.hMul.{u1, u1, u1} G₀ G₀ G₀ (instHMul.{u1} G₀ (MulZeroClass.toHasMul.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1))))) (HPow.hPow.{u1, 0, u1} G₀ Int G₀ (instHPow.{u1, 0} G₀ Int (DivInvMonoid.Pow.{u1} G₀ (GroupWithZero.toDivInvMonoid.{u1} G₀ _inst_1))) a n) (HPow.hPow.{u1, 0, u1} G₀ Int G₀ (instHPow.{u1, 0} G₀ Int (DivInvMonoid.Pow.{u1} G₀ (GroupWithZero.toDivInvMonoid.{u1} G₀ _inst_1))) a n)) a)
but is expected to have type
  forall {G₀ : Type.{u1}} [_inst_1 : GroupWithZero.{u1} G₀] (a : G₀) (n : Int), Eq.{succ u1} G₀ (HPow.hPow.{u1, 0, u1} G₀ Int G₀ (instHPow.{u1, 0} G₀ Int (DivInvMonoid.Pow.{u1} G₀ (GroupWithZero.toDivInvMonoid.{u1} G₀ _inst_1))) a (bit1.{0} Int (NonAssocRing.toOne.{0} Int (Ring.toNonAssocRing.{0} Int Int.instRingInt)) Int.instAddInt n)) (HMul.hMul.{u1, u1, u1} G₀ G₀ G₀ (instHMul.{u1} G₀ (MulZeroClass.toMul.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1))))) (HMul.hMul.{u1, u1, u1} G₀ G₀ G₀ (instHMul.{u1} G₀ (MulZeroClass.toMul.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1))))) (HPow.hPow.{u1, 0, u1} G₀ Int G₀ (instHPow.{u1, 0} G₀ Int (DivInvMonoid.Pow.{u1} G₀ (GroupWithZero.toDivInvMonoid.{u1} G₀ _inst_1))) a n) (HPow.hPow.{u1, 0, u1} G₀ Int G₀ (instHPow.{u1, 0} G₀ Int (DivInvMonoid.Pow.{u1} G₀ (GroupWithZero.toDivInvMonoid.{u1} G₀ _inst_1))) a n)) a)
Case conversion may be inaccurate. Consider using '#align zpow_bit1₀ zpow_bit1₀ₓ'. -/
theorem zpow_bit1₀ (a : G₀) (n : ℤ) : a ^ bit1 n = a ^ n * a ^ n * a :=
  by
  rw [← zpow_bit0, bit1, zpow_add', zpow_one]
  right; left
  apply bit1_ne_zero
#align zpow_bit1₀ zpow_bit1₀

/- warning: zpow_ne_zero_of_ne_zero -> zpow_ne_zero_of_ne_zero is a dubious translation:
lean 3 declaration is
  forall {G₀ : Type.{u1}} [_inst_1 : GroupWithZero.{u1} G₀] {a : G₀}, (Ne.{succ u1} G₀ a (OfNat.ofNat.{u1} G₀ 0 (OfNat.mk.{u1} G₀ 0 (Zero.zero.{u1} G₀ (MulZeroClass.toHasZero.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1)))))))) -> (forall (z : Int), Ne.{succ u1} G₀ (HPow.hPow.{u1, 0, u1} G₀ Int G₀ (instHPow.{u1, 0} G₀ Int (DivInvMonoid.Pow.{u1} G₀ (GroupWithZero.toDivInvMonoid.{u1} G₀ _inst_1))) a z) (OfNat.ofNat.{u1} G₀ 0 (OfNat.mk.{u1} G₀ 0 (Zero.zero.{u1} G₀ (MulZeroClass.toHasZero.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1))))))))
but is expected to have type
  forall {G₀ : Type.{u1}} [_inst_1 : GroupWithZero.{u1} G₀] {a : G₀}, (Ne.{succ u1} G₀ a (OfNat.ofNat.{u1} G₀ 0 (Zero.toOfNat0.{u1} G₀ (MonoidWithZero.toZero.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1))))) -> (forall (z : Int), Ne.{succ u1} G₀ (HPow.hPow.{u1, 0, u1} G₀ Int G₀ (instHPow.{u1, 0} G₀ Int (DivInvMonoid.Pow.{u1} G₀ (GroupWithZero.toDivInvMonoid.{u1} G₀ _inst_1))) a z) (OfNat.ofNat.{u1} G₀ 0 (Zero.toOfNat0.{u1} G₀ (MonoidWithZero.toZero.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1)))))
Case conversion may be inaccurate. Consider using '#align zpow_ne_zero_of_ne_zero zpow_ne_zero_of_ne_zeroₓ'. -/
theorem zpow_ne_zero_of_ne_zero {a : G₀} (ha : a ≠ 0) : ∀ z : ℤ, a ^ z ≠ 0
  | (n : ℕ) => by
    rw [zpow_ofNat]
    exact pow_ne_zero _ ha
  | -[n+1] => by
    rw [zpow_negSucc]
    exact inv_ne_zero (pow_ne_zero _ ha)
#align zpow_ne_zero_of_ne_zero zpow_ne_zero_of_ne_zero

/- warning: zpow_sub₀ -> zpow_sub₀ is a dubious translation:
lean 3 declaration is
  forall {G₀ : Type.{u1}} [_inst_1 : GroupWithZero.{u1} G₀] {a : G₀}, (Ne.{succ u1} G₀ a (OfNat.ofNat.{u1} G₀ 0 (OfNat.mk.{u1} G₀ 0 (Zero.zero.{u1} G₀ (MulZeroClass.toHasZero.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1)))))))) -> (forall (z1 : Int) (z2 : Int), Eq.{succ u1} G₀ (HPow.hPow.{u1, 0, u1} G₀ Int G₀ (instHPow.{u1, 0} G₀ Int (DivInvMonoid.Pow.{u1} G₀ (GroupWithZero.toDivInvMonoid.{u1} G₀ _inst_1))) a (HSub.hSub.{0, 0, 0} Int Int Int (instHSub.{0} Int Int.hasSub) z1 z2)) (HDiv.hDiv.{u1, u1, u1} G₀ G₀ G₀ (instHDiv.{u1} G₀ (DivInvMonoid.toHasDiv.{u1} G₀ (GroupWithZero.toDivInvMonoid.{u1} G₀ _inst_1))) (HPow.hPow.{u1, 0, u1} G₀ Int G₀ (instHPow.{u1, 0} G₀ Int (DivInvMonoid.Pow.{u1} G₀ (GroupWithZero.toDivInvMonoid.{u1} G₀ _inst_1))) a z1) (HPow.hPow.{u1, 0, u1} G₀ Int G₀ (instHPow.{u1, 0} G₀ Int (DivInvMonoid.Pow.{u1} G₀ (GroupWithZero.toDivInvMonoid.{u1} G₀ _inst_1))) a z2)))
but is expected to have type
  forall {G₀ : Type.{u1}} [_inst_1 : GroupWithZero.{u1} G₀] {a : G₀}, (Ne.{succ u1} G₀ a (OfNat.ofNat.{u1} G₀ 0 (Zero.toOfNat0.{u1} G₀ (MonoidWithZero.toZero.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1))))) -> (forall (z1 : Int) (z2 : Int), Eq.{succ u1} G₀ (HPow.hPow.{u1, 0, u1} G₀ Int G₀ (instHPow.{u1, 0} G₀ Int (DivInvMonoid.Pow.{u1} G₀ (GroupWithZero.toDivInvMonoid.{u1} G₀ _inst_1))) a (HSub.hSub.{0, 0, 0} Int Int Int (instHSub.{0} Int Int.instSubInt) z1 z2)) (HDiv.hDiv.{u1, u1, u1} G₀ G₀ G₀ (instHDiv.{u1} G₀ (GroupWithZero.toDiv.{u1} G₀ _inst_1)) (HPow.hPow.{u1, 0, u1} G₀ Int G₀ (instHPow.{u1, 0} G₀ Int (DivInvMonoid.Pow.{u1} G₀ (GroupWithZero.toDivInvMonoid.{u1} G₀ _inst_1))) a z1) (HPow.hPow.{u1, 0, u1} G₀ Int G₀ (instHPow.{u1, 0} G₀ Int (DivInvMonoid.Pow.{u1} G₀ (GroupWithZero.toDivInvMonoid.{u1} G₀ _inst_1))) a z2)))
Case conversion may be inaccurate. Consider using '#align zpow_sub₀ zpow_sub₀ₓ'. -/
theorem zpow_sub₀ {a : G₀} (ha : a ≠ 0) (z1 z2 : ℤ) : a ^ (z1 - z2) = a ^ z1 / a ^ z2 := by
  rw [sub_eq_add_neg, zpow_add₀ ha, zpow_neg, div_eq_mul_inv]
#align zpow_sub₀ zpow_sub₀

/- warning: zpow_bit1' -> zpow_bit1' is a dubious translation:
lean 3 declaration is
  forall {G₀ : Type.{u1}} [_inst_1 : GroupWithZero.{u1} G₀] (a : G₀) (n : Int), Eq.{succ u1} G₀ (HPow.hPow.{u1, 0, u1} G₀ Int G₀ (instHPow.{u1, 0} G₀ Int (DivInvMonoid.Pow.{u1} G₀ (GroupWithZero.toDivInvMonoid.{u1} G₀ _inst_1))) a (bit1.{0} Int Int.hasOne Int.hasAdd n)) (HMul.hMul.{u1, u1, u1} G₀ G₀ G₀ (instHMul.{u1} G₀ (MulZeroClass.toHasMul.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1))))) (HPow.hPow.{u1, 0, u1} G₀ Int G₀ (instHPow.{u1, 0} G₀ Int (DivInvMonoid.Pow.{u1} G₀ (GroupWithZero.toDivInvMonoid.{u1} G₀ _inst_1))) (HMul.hMul.{u1, u1, u1} G₀ G₀ G₀ (instHMul.{u1} G₀ (MulZeroClass.toHasMul.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1))))) a a) n) a)
but is expected to have type
  forall {G₀ : Type.{u1}} [_inst_1 : GroupWithZero.{u1} G₀] (a : G₀) (n : Int), Eq.{succ u1} G₀ (HPow.hPow.{u1, 0, u1} G₀ Int G₀ (instHPow.{u1, 0} G₀ Int (DivInvMonoid.Pow.{u1} G₀ (GroupWithZero.toDivInvMonoid.{u1} G₀ _inst_1))) a (bit1.{0} Int (NonAssocRing.toOne.{0} Int (Ring.toNonAssocRing.{0} Int Int.instRingInt)) Int.instAddInt n)) (HMul.hMul.{u1, u1, u1} G₀ G₀ G₀ (instHMul.{u1} G₀ (MulZeroClass.toMul.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1))))) (HPow.hPow.{u1, 0, u1} G₀ Int G₀ (instHPow.{u1, 0} G₀ Int (DivInvMonoid.Pow.{u1} G₀ (GroupWithZero.toDivInvMonoid.{u1} G₀ _inst_1))) (HMul.hMul.{u1, u1, u1} G₀ G₀ G₀ (instHMul.{u1} G₀ (MulZeroClass.toMul.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1))))) a a) n) a)
Case conversion may be inaccurate. Consider using '#align zpow_bit1' zpow_bit1'ₓ'. -/
theorem zpow_bit1' (a : G₀) (n : ℤ) : a ^ bit1 n = (a * a) ^ n * a := by
  rw [zpow_bit1₀, (Commute.refl a).mul_zpow]
#align zpow_bit1' zpow_bit1'

/- warning: zpow_eq_zero -> zpow_eq_zero is a dubious translation:
lean 3 declaration is
  forall {G₀ : Type.{u1}} [_inst_1 : GroupWithZero.{u1} G₀] {x : G₀} {n : Int}, (Eq.{succ u1} G₀ (HPow.hPow.{u1, 0, u1} G₀ Int G₀ (instHPow.{u1, 0} G₀ Int (DivInvMonoid.Pow.{u1} G₀ (GroupWithZero.toDivInvMonoid.{u1} G₀ _inst_1))) x n) (OfNat.ofNat.{u1} G₀ 0 (OfNat.mk.{u1} G₀ 0 (Zero.zero.{u1} G₀ (MulZeroClass.toHasZero.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1)))))))) -> (Eq.{succ u1} G₀ x (OfNat.ofNat.{u1} G₀ 0 (OfNat.mk.{u1} G₀ 0 (Zero.zero.{u1} G₀ (MulZeroClass.toHasZero.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1))))))))
but is expected to have type
  forall {G₀ : Type.{u1}} [_inst_1 : GroupWithZero.{u1} G₀] {x : G₀} {n : Int}, (Eq.{succ u1} G₀ (HPow.hPow.{u1, 0, u1} G₀ Int G₀ (instHPow.{u1, 0} G₀ Int (DivInvMonoid.Pow.{u1} G₀ (GroupWithZero.toDivInvMonoid.{u1} G₀ _inst_1))) x n) (OfNat.ofNat.{u1} G₀ 0 (Zero.toOfNat0.{u1} G₀ (MonoidWithZero.toZero.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1))))) -> (Eq.{succ u1} G₀ x (OfNat.ofNat.{u1} G₀ 0 (Zero.toOfNat0.{u1} G₀ (MonoidWithZero.toZero.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1)))))
Case conversion may be inaccurate. Consider using '#align zpow_eq_zero zpow_eq_zeroₓ'. -/
theorem zpow_eq_zero {x : G₀} {n : ℤ} (h : x ^ n = 0) : x = 0 :=
  by_contradiction fun hx => zpow_ne_zero_of_ne_zero hx n h
#align zpow_eq_zero zpow_eq_zero

/- warning: zpow_eq_zero_iff -> zpow_eq_zero_iff is a dubious translation:
lean 3 declaration is
  forall {G₀ : Type.{u1}} [_inst_1 : GroupWithZero.{u1} G₀] {a : G₀} {n : Int}, (Ne.{1} Int n (OfNat.ofNat.{0} Int 0 (OfNat.mk.{0} Int 0 (Zero.zero.{0} Int Int.hasZero)))) -> (Iff (Eq.{succ u1} G₀ (HPow.hPow.{u1, 0, u1} G₀ Int G₀ (instHPow.{u1, 0} G₀ Int (DivInvMonoid.Pow.{u1} G₀ (GroupWithZero.toDivInvMonoid.{u1} G₀ _inst_1))) a n) (OfNat.ofNat.{u1} G₀ 0 (OfNat.mk.{u1} G₀ 0 (Zero.zero.{u1} G₀ (MulZeroClass.toHasZero.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1)))))))) (Eq.{succ u1} G₀ a (OfNat.ofNat.{u1} G₀ 0 (OfNat.mk.{u1} G₀ 0 (Zero.zero.{u1} G₀ (MulZeroClass.toHasZero.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1)))))))))
but is expected to have type
  forall {G₀ : Type.{u1}} [_inst_1 : GroupWithZero.{u1} G₀] {a : G₀} {n : Int}, (Ne.{1} Int n (OfNat.ofNat.{0} Int 0 (instOfNatInt 0))) -> (Iff (Eq.{succ u1} G₀ (HPow.hPow.{u1, 0, u1} G₀ Int G₀ (instHPow.{u1, 0} G₀ Int (DivInvMonoid.Pow.{u1} G₀ (GroupWithZero.toDivInvMonoid.{u1} G₀ _inst_1))) a n) (OfNat.ofNat.{u1} G₀ 0 (Zero.toOfNat0.{u1} G₀ (MonoidWithZero.toZero.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1))))) (Eq.{succ u1} G₀ a (OfNat.ofNat.{u1} G₀ 0 (Zero.toOfNat0.{u1} G₀ (MonoidWithZero.toZero.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1))))))
Case conversion may be inaccurate. Consider using '#align zpow_eq_zero_iff zpow_eq_zero_iffₓ'. -/
theorem zpow_eq_zero_iff {a : G₀} {n : ℤ} (hn : n ≠ 0) : a ^ n = 0 ↔ a = 0 :=
  ⟨zpow_eq_zero, fun ha => ha.symm ▸ zero_zpow _ hn⟩
#align zpow_eq_zero_iff zpow_eq_zero_iff

/- warning: zpow_ne_zero -> zpow_ne_zero is a dubious translation:
lean 3 declaration is
  forall {G₀ : Type.{u1}} [_inst_1 : GroupWithZero.{u1} G₀] {x : G₀} (n : Int), (Ne.{succ u1} G₀ x (OfNat.ofNat.{u1} G₀ 0 (OfNat.mk.{u1} G₀ 0 (Zero.zero.{u1} G₀ (MulZeroClass.toHasZero.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1)))))))) -> (Ne.{succ u1} G₀ (HPow.hPow.{u1, 0, u1} G₀ Int G₀ (instHPow.{u1, 0} G₀ Int (DivInvMonoid.Pow.{u1} G₀ (GroupWithZero.toDivInvMonoid.{u1} G₀ _inst_1))) x n) (OfNat.ofNat.{u1} G₀ 0 (OfNat.mk.{u1} G₀ 0 (Zero.zero.{u1} G₀ (MulZeroClass.toHasZero.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1))))))))
but is expected to have type
  forall {G₀ : Type.{u1}} [_inst_1 : GroupWithZero.{u1} G₀] {x : G₀} (n : Int), (Ne.{succ u1} G₀ x (OfNat.ofNat.{u1} G₀ 0 (Zero.toOfNat0.{u1} G₀ (MonoidWithZero.toZero.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1))))) -> (Ne.{succ u1} G₀ (HPow.hPow.{u1, 0, u1} G₀ Int G₀ (instHPow.{u1, 0} G₀ Int (DivInvMonoid.Pow.{u1} G₀ (GroupWithZero.toDivInvMonoid.{u1} G₀ _inst_1))) x n) (OfNat.ofNat.{u1} G₀ 0 (Zero.toOfNat0.{u1} G₀ (MonoidWithZero.toZero.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1)))))
Case conversion may be inaccurate. Consider using '#align zpow_ne_zero zpow_ne_zeroₓ'. -/
theorem zpow_ne_zero {x : G₀} (n : ℤ) : x ≠ 0 → x ^ n ≠ 0 :=
  mt zpow_eq_zero
#align zpow_ne_zero zpow_ne_zero

/- warning: zpow_neg_mul_zpow_self -> zpow_neg_mul_zpow_self is a dubious translation:
lean 3 declaration is
  forall {G₀ : Type.{u1}} [_inst_1 : GroupWithZero.{u1} G₀] (n : Int) {x : G₀}, (Ne.{succ u1} G₀ x (OfNat.ofNat.{u1} G₀ 0 (OfNat.mk.{u1} G₀ 0 (Zero.zero.{u1} G₀ (MulZeroClass.toHasZero.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1)))))))) -> (Eq.{succ u1} G₀ (HMul.hMul.{u1, u1, u1} G₀ G₀ G₀ (instHMul.{u1} G₀ (MulZeroClass.toHasMul.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1))))) (HPow.hPow.{u1, 0, u1} G₀ Int G₀ (instHPow.{u1, 0} G₀ Int (DivInvMonoid.Pow.{u1} G₀ (GroupWithZero.toDivInvMonoid.{u1} G₀ _inst_1))) x (Neg.neg.{0} Int Int.hasNeg n)) (HPow.hPow.{u1, 0, u1} G₀ Int G₀ (instHPow.{u1, 0} G₀ Int (DivInvMonoid.Pow.{u1} G₀ (GroupWithZero.toDivInvMonoid.{u1} G₀ _inst_1))) x n)) (OfNat.ofNat.{u1} G₀ 1 (OfNat.mk.{u1} G₀ 1 (One.one.{u1} G₀ (MulOneClass.toHasOne.{u1} G₀ (MulZeroOneClass.toMulOneClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1))))))))
but is expected to have type
  forall {G₀ : Type.{u1}} [_inst_1 : GroupWithZero.{u1} G₀] (n : Int) {x : G₀}, (Ne.{succ u1} G₀ x (OfNat.ofNat.{u1} G₀ 0 (Zero.toOfNat0.{u1} G₀ (MonoidWithZero.toZero.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1))))) -> (Eq.{succ u1} G₀ (HMul.hMul.{u1, u1, u1} G₀ G₀ G₀ (instHMul.{u1} G₀ (MulZeroClass.toMul.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1))))) (HPow.hPow.{u1, 0, u1} G₀ Int G₀ (instHPow.{u1, 0} G₀ Int (DivInvMonoid.Pow.{u1} G₀ (GroupWithZero.toDivInvMonoid.{u1} G₀ _inst_1))) x (Neg.neg.{0} Int Int.instNegInt n)) (HPow.hPow.{u1, 0, u1} G₀ Int G₀ (instHPow.{u1, 0} G₀ Int (DivInvMonoid.Pow.{u1} G₀ (GroupWithZero.toDivInvMonoid.{u1} G₀ _inst_1))) x n)) (OfNat.ofNat.{u1} G₀ 1 (One.toOfNat1.{u1} G₀ (InvOneClass.toOne.{u1} G₀ (DivInvOneMonoid.toInvOneClass.{u1} G₀ (DivisionMonoid.toDivInvOneMonoid.{u1} G₀ (GroupWithZero.toDivisionMonoid.{u1} G₀ _inst_1)))))))
Case conversion may be inaccurate. Consider using '#align zpow_neg_mul_zpow_self zpow_neg_mul_zpow_selfₓ'. -/
theorem zpow_neg_mul_zpow_self (n : ℤ) {x : G₀} (h : x ≠ 0) : x ^ (-n) * x ^ n = 1 :=
  by
  rw [zpow_neg]
  exact inv_mul_cancel (zpow_ne_zero n h)
#align zpow_neg_mul_zpow_self zpow_neg_mul_zpow_self

end Zpow

section

variable {G₀ : Type _} [CommGroupWithZero G₀]

/- warning: div_sq_cancel -> div_sq_cancel is a dubious translation:
lean 3 declaration is
  forall {G₀ : Type.{u1}} [_inst_1 : CommGroupWithZero.{u1} G₀] (a : G₀) (b : G₀), Eq.{succ u1} G₀ (HDiv.hDiv.{u1, u1, u1} G₀ G₀ G₀ (instHDiv.{u1} G₀ (DivInvMonoid.toHasDiv.{u1} G₀ (GroupWithZero.toDivInvMonoid.{u1} G₀ (CommGroupWithZero.toGroupWithZero.{u1} G₀ _inst_1)))) (HMul.hMul.{u1, u1, u1} G₀ G₀ G₀ (instHMul.{u1} G₀ (MulZeroClass.toHasMul.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ (CommGroupWithZero.toGroupWithZero.{u1} G₀ _inst_1)))))) (HPow.hPow.{u1, 0, u1} G₀ Nat G₀ (instHPow.{u1, 0} G₀ Nat (Monoid.Pow.{u1} G₀ (MonoidWithZero.toMonoid.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ (CommGroupWithZero.toGroupWithZero.{u1} G₀ _inst_1))))) a (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) b) a) (HMul.hMul.{u1, u1, u1} G₀ G₀ G₀ (instHMul.{u1} G₀ (MulZeroClass.toHasMul.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ (CommGroupWithZero.toGroupWithZero.{u1} G₀ _inst_1)))))) a b)
but is expected to have type
  forall {G₀ : Type.{u1}} [_inst_1 : CommGroupWithZero.{u1} G₀] (a : G₀) (b : G₀), Eq.{succ u1} G₀ (HDiv.hDiv.{u1, u1, u1} G₀ G₀ G₀ (instHDiv.{u1} G₀ (CommGroupWithZero.toDiv.{u1} G₀ _inst_1)) (HMul.hMul.{u1, u1, u1} G₀ G₀ G₀ (instHMul.{u1} G₀ (MulZeroClass.toMul.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ (CommGroupWithZero.toGroupWithZero.{u1} G₀ _inst_1)))))) (HPow.hPow.{u1, 0, u1} G₀ Nat G₀ (instHPow.{u1, 0} G₀ Nat (Monoid.Pow.{u1} G₀ (MonoidWithZero.toMonoid.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ (CommGroupWithZero.toGroupWithZero.{u1} G₀ _inst_1))))) a (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) b) a) (HMul.hMul.{u1, u1, u1} G₀ G₀ G₀ (instHMul.{u1} G₀ (MulZeroClass.toMul.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ (CommGroupWithZero.toGroupWithZero.{u1} G₀ _inst_1)))))) a b)
Case conversion may be inaccurate. Consider using '#align div_sq_cancel div_sq_cancelₓ'. -/
theorem div_sq_cancel (a b : G₀) : a ^ 2 * b / a = a * b :=
  by
  by_cases ha : a = 0
  · simp [ha]
  rw [sq, mul_assoc, mul_div_cancel_left _ ha]
#align div_sq_cancel div_sq_cancel

end

/- warning: map_zpow₀ -> map_zpow₀ is a dubious translation:
lean 3 declaration is
  forall {F : Type.{u1}} {G₀ : Type.{u2}} {G₀' : Type.{u3}} [_inst_1 : GroupWithZero.{u2} G₀] [_inst_2 : GroupWithZero.{u3} G₀'] [_inst_3 : MonoidWithZeroHomClass.{u1, u2, u3} F G₀ G₀' (MonoidWithZero.toMulZeroOneClass.{u2} G₀ (GroupWithZero.toMonoidWithZero.{u2} G₀ _inst_1)) (MonoidWithZero.toMulZeroOneClass.{u3} G₀' (GroupWithZero.toMonoidWithZero.{u3} G₀' _inst_2))] (f : F) (x : G₀) (n : Int), Eq.{succ u3} G₀' (coeFn.{succ u1, max (succ u2) (succ u3)} F (fun (_x : F) => G₀ -> G₀') (FunLike.hasCoeToFun.{succ u1, succ u2, succ u3} F G₀ (fun (_x : G₀) => G₀') (MulHomClass.toFunLike.{u1, u2, u3} F G₀ G₀' (MulOneClass.toHasMul.{u2} G₀ (MulZeroOneClass.toMulOneClass.{u2} G₀ (MonoidWithZero.toMulZeroOneClass.{u2} G₀ (GroupWithZero.toMonoidWithZero.{u2} G₀ _inst_1)))) (MulOneClass.toHasMul.{u3} G₀' (MulZeroOneClass.toMulOneClass.{u3} G₀' (MonoidWithZero.toMulZeroOneClass.{u3} G₀' (GroupWithZero.toMonoidWithZero.{u3} G₀' _inst_2)))) (MonoidHomClass.toMulHomClass.{u1, u2, u3} F G₀ G₀' (MulZeroOneClass.toMulOneClass.{u2} G₀ (MonoidWithZero.toMulZeroOneClass.{u2} G₀ (GroupWithZero.toMonoidWithZero.{u2} G₀ _inst_1))) (MulZeroOneClass.toMulOneClass.{u3} G₀' (MonoidWithZero.toMulZeroOneClass.{u3} G₀' (GroupWithZero.toMonoidWithZero.{u3} G₀' _inst_2))) (MonoidWithZeroHomClass.toMonoidHomClass.{u1, u2, u3} F G₀ G₀' (MonoidWithZero.toMulZeroOneClass.{u2} G₀ (GroupWithZero.toMonoidWithZero.{u2} G₀ _inst_1)) (MonoidWithZero.toMulZeroOneClass.{u3} G₀' (GroupWithZero.toMonoidWithZero.{u3} G₀' _inst_2)) _inst_3)))) f (HPow.hPow.{u2, 0, u2} G₀ Int G₀ (instHPow.{u2, 0} G₀ Int (DivInvMonoid.Pow.{u2} G₀ (GroupWithZero.toDivInvMonoid.{u2} G₀ _inst_1))) x n)) (HPow.hPow.{u3, 0, u3} G₀' Int G₀' (instHPow.{u3, 0} G₀' Int (DivInvMonoid.Pow.{u3} G₀' (GroupWithZero.toDivInvMonoid.{u3} G₀' _inst_2))) (coeFn.{succ u1, max (succ u2) (succ u3)} F (fun (_x : F) => G₀ -> G₀') (FunLike.hasCoeToFun.{succ u1, succ u2, succ u3} F G₀ (fun (_x : G₀) => G₀') (MulHomClass.toFunLike.{u1, u2, u3} F G₀ G₀' (MulOneClass.toHasMul.{u2} G₀ (MulZeroOneClass.toMulOneClass.{u2} G₀ (MonoidWithZero.toMulZeroOneClass.{u2} G₀ (GroupWithZero.toMonoidWithZero.{u2} G₀ _inst_1)))) (MulOneClass.toHasMul.{u3} G₀' (MulZeroOneClass.toMulOneClass.{u3} G₀' (MonoidWithZero.toMulZeroOneClass.{u3} G₀' (GroupWithZero.toMonoidWithZero.{u3} G₀' _inst_2)))) (MonoidHomClass.toMulHomClass.{u1, u2, u3} F G₀ G₀' (MulZeroOneClass.toMulOneClass.{u2} G₀ (MonoidWithZero.toMulZeroOneClass.{u2} G₀ (GroupWithZero.toMonoidWithZero.{u2} G₀ _inst_1))) (MulZeroOneClass.toMulOneClass.{u3} G₀' (MonoidWithZero.toMulZeroOneClass.{u3} G₀' (GroupWithZero.toMonoidWithZero.{u3} G₀' _inst_2))) (MonoidWithZeroHomClass.toMonoidHomClass.{u1, u2, u3} F G₀ G₀' (MonoidWithZero.toMulZeroOneClass.{u2} G₀ (GroupWithZero.toMonoidWithZero.{u2} G₀ _inst_1)) (MonoidWithZero.toMulZeroOneClass.{u3} G₀' (GroupWithZero.toMonoidWithZero.{u3} G₀' _inst_2)) _inst_3)))) f x) n)
but is expected to have type
  forall {F : Type.{u3}} {G₀ : Type.{u2}} {G₀' : Type.{u1}} [_inst_1 : GroupWithZero.{u2} G₀] [_inst_2 : GroupWithZero.{u1} G₀'] [_inst_3 : MonoidWithZeroHomClass.{u3, u2, u1} F G₀ G₀' (MonoidWithZero.toMulZeroOneClass.{u2} G₀ (GroupWithZero.toMonoidWithZero.{u2} G₀ _inst_1)) (MonoidWithZero.toMulZeroOneClass.{u1} G₀' (GroupWithZero.toMonoidWithZero.{u1} G₀' _inst_2))] (f : F) (x : G₀) (n : Int), Eq.{succ u1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : G₀) => G₀') (HPow.hPow.{u2, 0, u2} G₀ Int G₀ (instHPow.{u2, 0} G₀ Int (DivInvMonoid.Pow.{u2} G₀ (GroupWithZero.toDivInvMonoid.{u2} G₀ _inst_1))) x n)) (FunLike.coe.{succ u3, succ u2, succ u1} F G₀ (fun (_x : G₀) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : G₀) => G₀') _x) (MulHomClass.toFunLike.{u3, u2, u1} F G₀ G₀' (MulOneClass.toMul.{u2} G₀ (MulZeroOneClass.toMulOneClass.{u2} G₀ (MonoidWithZero.toMulZeroOneClass.{u2} G₀ (GroupWithZero.toMonoidWithZero.{u2} G₀ _inst_1)))) (MulOneClass.toMul.{u1} G₀' (MulZeroOneClass.toMulOneClass.{u1} G₀' (MonoidWithZero.toMulZeroOneClass.{u1} G₀' (GroupWithZero.toMonoidWithZero.{u1} G₀' _inst_2)))) (MonoidHomClass.toMulHomClass.{u3, u2, u1} F G₀ G₀' (MulZeroOneClass.toMulOneClass.{u2} G₀ (MonoidWithZero.toMulZeroOneClass.{u2} G₀ (GroupWithZero.toMonoidWithZero.{u2} G₀ _inst_1))) (MulZeroOneClass.toMulOneClass.{u1} G₀' (MonoidWithZero.toMulZeroOneClass.{u1} G₀' (GroupWithZero.toMonoidWithZero.{u1} G₀' _inst_2))) (MonoidWithZeroHomClass.toMonoidHomClass.{u3, u2, u1} F G₀ G₀' (MonoidWithZero.toMulZeroOneClass.{u2} G₀ (GroupWithZero.toMonoidWithZero.{u2} G₀ _inst_1)) (MonoidWithZero.toMulZeroOneClass.{u1} G₀' (GroupWithZero.toMonoidWithZero.{u1} G₀' _inst_2)) _inst_3))) f (HPow.hPow.{u2, 0, u2} G₀ Int G₀ (instHPow.{u2, 0} G₀ Int (DivInvMonoid.Pow.{u2} G₀ (GroupWithZero.toDivInvMonoid.{u2} G₀ _inst_1))) x n)) (HPow.hPow.{u1, 0, u1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : G₀) => G₀') x) Int ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : G₀) => G₀') x) (instHPow.{u1, 0} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : G₀) => G₀') x) Int (DivInvMonoid.Pow.{u1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : G₀) => G₀') x) (GroupWithZero.toDivInvMonoid.{u1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : G₀) => G₀') x) _inst_2))) (FunLike.coe.{succ u3, succ u2, succ u1} F G₀ (fun (_x : G₀) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : G₀) => G₀') _x) (MulHomClass.toFunLike.{u3, u2, u1} F G₀ G₀' (MulOneClass.toMul.{u2} G₀ (MulZeroOneClass.toMulOneClass.{u2} G₀ (MonoidWithZero.toMulZeroOneClass.{u2} G₀ (GroupWithZero.toMonoidWithZero.{u2} G₀ _inst_1)))) (MulOneClass.toMul.{u1} G₀' (MulZeroOneClass.toMulOneClass.{u1} G₀' (MonoidWithZero.toMulZeroOneClass.{u1} G₀' (GroupWithZero.toMonoidWithZero.{u1} G₀' _inst_2)))) (MonoidHomClass.toMulHomClass.{u3, u2, u1} F G₀ G₀' (MulZeroOneClass.toMulOneClass.{u2} G₀ (MonoidWithZero.toMulZeroOneClass.{u2} G₀ (GroupWithZero.toMonoidWithZero.{u2} G₀ _inst_1))) (MulZeroOneClass.toMulOneClass.{u1} G₀' (MonoidWithZero.toMulZeroOneClass.{u1} G₀' (GroupWithZero.toMonoidWithZero.{u1} G₀' _inst_2))) (MonoidWithZeroHomClass.toMonoidHomClass.{u3, u2, u1} F G₀ G₀' (MonoidWithZero.toMulZeroOneClass.{u2} G₀ (GroupWithZero.toMonoidWithZero.{u2} G₀ _inst_1)) (MonoidWithZero.toMulZeroOneClass.{u1} G₀' (GroupWithZero.toMonoidWithZero.{u1} G₀' _inst_2)) _inst_3))) f x) n)
Case conversion may be inaccurate. Consider using '#align map_zpow₀ map_zpow₀ₓ'. -/
/-- If a monoid homomorphism `f` between two `group_with_zero`s maps `0` to `0`, then it maps `x^n`,
`n : ℤ`, to `(f x)^n`. -/
@[simp]
theorem map_zpow₀ {F G₀ G₀' : Type _} [GroupWithZero G₀] [GroupWithZero G₀']
    [MonoidWithZeroHomClass F G₀ G₀'] (f : F) (x : G₀) (n : ℤ) : f (x ^ n) = f x ^ n :=
  map_zpow' f (map_inv₀ f) x n
#align map_zpow₀ map_zpow₀

