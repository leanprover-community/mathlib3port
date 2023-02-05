/-
Copyright (c) 2018 Louis Carlin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Louis Carlin, Mario Carneiro

! This file was ported from Lean 3 source module algebra.euclidean_domain.basic
! leanprover-community/mathlib commit 4c19a16e4b705bf135cf9a80ac18fcc99c438514
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.EuclideanDomain.Defs
import Mathbin.Algebra.Ring.Divisibility
import Mathbin.Algebra.Ring.Regular
import Mathbin.Algebra.GroupWithZero.Divisibility
import Mathbin.Algebra.Ring.Basic

/-!
# Lemmas about Euclidean domains

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

## Main statements

* `gcd_eq_gcd_ab`: states Bézout's lemma for Euclidean domains.

-/


universe u

namespace EuclideanDomain

variable {R : Type u}

variable [EuclideanDomain R]

-- mathport name: «expr ≺ »
local infixl:50 " ≺ " => EuclideanDomain.r

/- warning: euclidean_domain.mul_div_cancel_left -> EuclideanDomain.mul_div_cancel_left is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : EuclideanDomain.{u1} R] {a : R} (b : R), (Ne.{succ u1} R a (OfNat.ofNat.{u1} R 0 (OfNat.mk.{u1} R 0 (Zero.zero.{u1} R (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R (EuclideanDomain.toCommRing.{u1} R _inst_1))))))))))) -> (Eq.{succ u1} R (HDiv.hDiv.{u1, u1, u1} R R R (instHDiv.{u1} R (EuclideanDomain.hasDiv.{u1} R _inst_1)) (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (Distrib.toHasMul.{u1} R (Ring.toDistrib.{u1} R (CommRing.toRing.{u1} R (EuclideanDomain.toCommRing.{u1} R _inst_1))))) a b) a) b)
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : EuclideanDomain.{u1} R] {a : R} (b : R), (Ne.{succ u1} R a (OfNat.ofNat.{u1} R 0 (Zero.toOfNat0.{u1} R (CommMonoidWithZero.toZero.{u1} R (CommSemiring.toCommMonoidWithZero.{u1} R (CommRing.toCommSemiring.{u1} R (EuclideanDomain.toCommRing.{u1} R _inst_1))))))) -> (Eq.{succ u1} R (HDiv.hDiv.{u1, u1, u1} R R R (instHDiv.{u1} R (EuclideanDomain.instDiv.{u1} R _inst_1)) (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (NonUnitalNonAssocRing.toMul.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R (EuclideanDomain.toCommRing.{u1} R _inst_1)))))) a b) a) b)
Case conversion may be inaccurate. Consider using '#align euclidean_domain.mul_div_cancel_left EuclideanDomain.mul_div_cancel_leftₓ'. -/
theorem mul_div_cancel_left {a : R} (b) (a0 : a ≠ 0) : a * b / a = b :=
  Eq.symm <|
    eq_of_sub_eq_zero <|
      by_contradiction fun h => by
        have := mul_left_not_lt a h
        rw [mul_sub, sub_eq_iff_eq_add'.2 (div_add_mod (a * b) a).symm] at this
        exact this (mod_lt _ a0)
#align euclidean_domain.mul_div_cancel_left EuclideanDomain.mul_div_cancel_left

/- warning: euclidean_domain.mul_div_cancel -> EuclideanDomain.mul_div_cancel is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : EuclideanDomain.{u1} R] (a : R) {b : R}, (Ne.{succ u1} R b (OfNat.ofNat.{u1} R 0 (OfNat.mk.{u1} R 0 (Zero.zero.{u1} R (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R (EuclideanDomain.toCommRing.{u1} R _inst_1))))))))))) -> (Eq.{succ u1} R (HDiv.hDiv.{u1, u1, u1} R R R (instHDiv.{u1} R (EuclideanDomain.hasDiv.{u1} R _inst_1)) (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (Distrib.toHasMul.{u1} R (Ring.toDistrib.{u1} R (CommRing.toRing.{u1} R (EuclideanDomain.toCommRing.{u1} R _inst_1))))) a b) b) a)
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : EuclideanDomain.{u1} R] (a : R) {b : R}, (Ne.{succ u1} R b (OfNat.ofNat.{u1} R 0 (Zero.toOfNat0.{u1} R (CommMonoidWithZero.toZero.{u1} R (CommSemiring.toCommMonoidWithZero.{u1} R (CommRing.toCommSemiring.{u1} R (EuclideanDomain.toCommRing.{u1} R _inst_1))))))) -> (Eq.{succ u1} R (HDiv.hDiv.{u1, u1, u1} R R R (instHDiv.{u1} R (EuclideanDomain.instDiv.{u1} R _inst_1)) (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (NonUnitalNonAssocRing.toMul.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R (EuclideanDomain.toCommRing.{u1} R _inst_1)))))) a b) b) a)
Case conversion may be inaccurate. Consider using '#align euclidean_domain.mul_div_cancel EuclideanDomain.mul_div_cancelₓ'. -/
theorem mul_div_cancel (a) {b : R} (b0 : b ≠ 0) : a * b / b = a :=
  by
  rw [mul_comm]
  exact mul_div_cancel_left a b0
#align euclidean_domain.mul_div_cancel EuclideanDomain.mul_div_cancel

/- warning: euclidean_domain.mod_eq_zero -> EuclideanDomain.mod_eq_zero is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : EuclideanDomain.{u1} R] {a : R} {b : R}, Iff (Eq.{succ u1} R (HMod.hMod.{u1, u1, u1} R R R (instHMod.{u1} R (EuclideanDomain.hasMod.{u1} R _inst_1)) a b) (OfNat.ofNat.{u1} R 0 (OfNat.mk.{u1} R 0 (Zero.zero.{u1} R (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R (EuclideanDomain.toCommRing.{u1} R _inst_1))))))))))) (Dvd.Dvd.{u1} R (semigroupDvd.{u1} R (SemigroupWithZero.toSemigroup.{u1} R (NonUnitalSemiring.toSemigroupWithZero.{u1} R (NonUnitalRing.toNonUnitalSemiring.{u1} R (NonUnitalCommRing.toNonUnitalRing.{u1} R (CommRing.toNonUnitalCommRing.{u1} R (EuclideanDomain.toCommRing.{u1} R _inst_1))))))) b a)
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : EuclideanDomain.{u1} R] {a : R} {b : R}, Iff (Eq.{succ u1} R (HMod.hMod.{u1, u1, u1} R R R (instHMod.{u1} R (EuclideanDomain.instMod.{u1} R _inst_1)) a b) (OfNat.ofNat.{u1} R 0 (Zero.toOfNat0.{u1} R (CommMonoidWithZero.toZero.{u1} R (CommSemiring.toCommMonoidWithZero.{u1} R (CommRing.toCommSemiring.{u1} R (EuclideanDomain.toCommRing.{u1} R _inst_1))))))) (Dvd.dvd.{u1} R (semigroupDvd.{u1} R (SemigroupWithZero.toSemigroup.{u1} R (NonUnitalSemiring.toSemigroupWithZero.{u1} R (NonUnitalRing.toNonUnitalSemiring.{u1} R (NonUnitalCommRing.toNonUnitalRing.{u1} R (CommRing.toNonUnitalCommRing.{u1} R (EuclideanDomain.toCommRing.{u1} R _inst_1))))))) b a)
Case conversion may be inaccurate. Consider using '#align euclidean_domain.mod_eq_zero EuclideanDomain.mod_eq_zeroₓ'. -/
@[simp]
theorem mod_eq_zero {a b : R} : a % b = 0 ↔ b ∣ a :=
  ⟨fun h => by
    rw [← div_add_mod a b, h, add_zero]
    exact dvd_mul_right _ _, fun ⟨c, e⟩ =>
    by
    rw [e, ← add_left_cancel_iff, div_add_mod, add_zero]
    haveI := Classical.dec
    by_cases b0 : b = 0
    · simp only [b0, zero_mul]
    · rw [mul_div_cancel_left _ b0]⟩
#align euclidean_domain.mod_eq_zero EuclideanDomain.mod_eq_zero

/- warning: euclidean_domain.mod_self -> EuclideanDomain.mod_self is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : EuclideanDomain.{u1} R] (a : R), Eq.{succ u1} R (HMod.hMod.{u1, u1, u1} R R R (instHMod.{u1} R (EuclideanDomain.hasMod.{u1} R _inst_1)) a a) (OfNat.ofNat.{u1} R 0 (OfNat.mk.{u1} R 0 (Zero.zero.{u1} R (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R (EuclideanDomain.toCommRing.{u1} R _inst_1))))))))))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : EuclideanDomain.{u1} R] (a : R), Eq.{succ u1} R (HMod.hMod.{u1, u1, u1} R R R (instHMod.{u1} R (EuclideanDomain.instMod.{u1} R _inst_1)) a a) (OfNat.ofNat.{u1} R 0 (Zero.toOfNat0.{u1} R (CommMonoidWithZero.toZero.{u1} R (CommSemiring.toCommMonoidWithZero.{u1} R (CommRing.toCommSemiring.{u1} R (EuclideanDomain.toCommRing.{u1} R _inst_1))))))
Case conversion may be inaccurate. Consider using '#align euclidean_domain.mod_self EuclideanDomain.mod_selfₓ'. -/
@[simp]
theorem mod_self (a : R) : a % a = 0 :=
  mod_eq_zero.2 dvd_rfl
#align euclidean_domain.mod_self EuclideanDomain.mod_self

#print EuclideanDomain.dvd_mod_iff /-
theorem dvd_mod_iff {a b c : R} (h : c ∣ b) : c ∣ a % b ↔ c ∣ a := by
  rw [dvd_add_iff_right (h.mul_right _), div_add_mod]
#align euclidean_domain.dvd_mod_iff EuclideanDomain.dvd_mod_iff
-/

/- warning: euclidean_domain.mod_one -> EuclideanDomain.mod_one is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : EuclideanDomain.{u1} R] (a : R), Eq.{succ u1} R (HMod.hMod.{u1, u1, u1} R R R (instHMod.{u1} R (EuclideanDomain.hasMod.{u1} R _inst_1)) a (OfNat.ofNat.{u1} R 1 (OfNat.mk.{u1} R 1 (One.one.{u1} R (AddMonoidWithOne.toOne.{u1} R (AddGroupWithOne.toAddMonoidWithOne.{u1} R (NonAssocRing.toAddGroupWithOne.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R (EuclideanDomain.toCommRing.{u1} R _inst_1)))))))))) (OfNat.ofNat.{u1} R 0 (OfNat.mk.{u1} R 0 (Zero.zero.{u1} R (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R (EuclideanDomain.toCommRing.{u1} R _inst_1))))))))))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : EuclideanDomain.{u1} R] (a : R), Eq.{succ u1} R (HMod.hMod.{u1, u1, u1} R R R (instHMod.{u1} R (EuclideanDomain.instMod.{u1} R _inst_1)) a (OfNat.ofNat.{u1} R 1 (One.toOfNat1.{u1} R (NonAssocRing.toOne.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R (EuclideanDomain.toCommRing.{u1} R _inst_1))))))) (OfNat.ofNat.{u1} R 0 (Zero.toOfNat0.{u1} R (CommMonoidWithZero.toZero.{u1} R (CommSemiring.toCommMonoidWithZero.{u1} R (CommRing.toCommSemiring.{u1} R (EuclideanDomain.toCommRing.{u1} R _inst_1))))))
Case conversion may be inaccurate. Consider using '#align euclidean_domain.mod_one EuclideanDomain.mod_oneₓ'. -/
@[simp]
theorem mod_one (a : R) : a % 1 = 0 :=
  mod_eq_zero.2 (one_dvd _)
#align euclidean_domain.mod_one EuclideanDomain.mod_one

/- warning: euclidean_domain.zero_mod -> EuclideanDomain.zero_mod is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : EuclideanDomain.{u1} R] (b : R), Eq.{succ u1} R (HMod.hMod.{u1, u1, u1} R R R (instHMod.{u1} R (EuclideanDomain.hasMod.{u1} R _inst_1)) (OfNat.ofNat.{u1} R 0 (OfNat.mk.{u1} R 0 (Zero.zero.{u1} R (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R (EuclideanDomain.toCommRing.{u1} R _inst_1)))))))))) b) (OfNat.ofNat.{u1} R 0 (OfNat.mk.{u1} R 0 (Zero.zero.{u1} R (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R (EuclideanDomain.toCommRing.{u1} R _inst_1))))))))))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : EuclideanDomain.{u1} R] (b : R), Eq.{succ u1} R (HMod.hMod.{u1, u1, u1} R R R (instHMod.{u1} R (EuclideanDomain.instMod.{u1} R _inst_1)) (OfNat.ofNat.{u1} R 0 (Zero.toOfNat0.{u1} R (CommMonoidWithZero.toZero.{u1} R (CommSemiring.toCommMonoidWithZero.{u1} R (CommRing.toCommSemiring.{u1} R (EuclideanDomain.toCommRing.{u1} R _inst_1)))))) b) (OfNat.ofNat.{u1} R 0 (Zero.toOfNat0.{u1} R (CommMonoidWithZero.toZero.{u1} R (CommSemiring.toCommMonoidWithZero.{u1} R (CommRing.toCommSemiring.{u1} R (EuclideanDomain.toCommRing.{u1} R _inst_1))))))
Case conversion may be inaccurate. Consider using '#align euclidean_domain.zero_mod EuclideanDomain.zero_modₓ'. -/
@[simp]
theorem zero_mod (b : R) : 0 % b = 0 :=
  mod_eq_zero.2 (dvd_zero _)
#align euclidean_domain.zero_mod EuclideanDomain.zero_mod

/- warning: euclidean_domain.zero_div -> EuclideanDomain.zero_div is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : EuclideanDomain.{u1} R] {a : R}, Eq.{succ u1} R (HDiv.hDiv.{u1, u1, u1} R R R (instHDiv.{u1} R (EuclideanDomain.hasDiv.{u1} R _inst_1)) (OfNat.ofNat.{u1} R 0 (OfNat.mk.{u1} R 0 (Zero.zero.{u1} R (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R (EuclideanDomain.toCommRing.{u1} R _inst_1)))))))))) a) (OfNat.ofNat.{u1} R 0 (OfNat.mk.{u1} R 0 (Zero.zero.{u1} R (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R (EuclideanDomain.toCommRing.{u1} R _inst_1))))))))))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : EuclideanDomain.{u1} R] {a : R}, Eq.{succ u1} R (HDiv.hDiv.{u1, u1, u1} R R R (instHDiv.{u1} R (EuclideanDomain.instDiv.{u1} R _inst_1)) (OfNat.ofNat.{u1} R 0 (Zero.toOfNat0.{u1} R (CommMonoidWithZero.toZero.{u1} R (CommSemiring.toCommMonoidWithZero.{u1} R (CommRing.toCommSemiring.{u1} R (EuclideanDomain.toCommRing.{u1} R _inst_1)))))) a) (OfNat.ofNat.{u1} R 0 (Zero.toOfNat0.{u1} R (CommMonoidWithZero.toZero.{u1} R (CommSemiring.toCommMonoidWithZero.{u1} R (CommRing.toCommSemiring.{u1} R (EuclideanDomain.toCommRing.{u1} R _inst_1))))))
Case conversion may be inaccurate. Consider using '#align euclidean_domain.zero_div EuclideanDomain.zero_divₓ'. -/
@[simp]
theorem zero_div {a : R} : 0 / a = 0 :=
  by_cases (fun a0 : a = 0 => a0.symm ▸ div_zero 0) fun a0 => by
    simpa only [zero_mul] using mul_div_cancel 0 a0
#align euclidean_domain.zero_div EuclideanDomain.zero_div

/- warning: euclidean_domain.div_self -> EuclideanDomain.div_self is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : EuclideanDomain.{u1} R] {a : R}, (Ne.{succ u1} R a (OfNat.ofNat.{u1} R 0 (OfNat.mk.{u1} R 0 (Zero.zero.{u1} R (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R (EuclideanDomain.toCommRing.{u1} R _inst_1))))))))))) -> (Eq.{succ u1} R (HDiv.hDiv.{u1, u1, u1} R R R (instHDiv.{u1} R (EuclideanDomain.hasDiv.{u1} R _inst_1)) a a) (OfNat.ofNat.{u1} R 1 (OfNat.mk.{u1} R 1 (One.one.{u1} R (AddMonoidWithOne.toOne.{u1} R (AddGroupWithOne.toAddMonoidWithOne.{u1} R (NonAssocRing.toAddGroupWithOne.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R (EuclideanDomain.toCommRing.{u1} R _inst_1))))))))))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : EuclideanDomain.{u1} R] {a : R}, (Ne.{succ u1} R a (OfNat.ofNat.{u1} R 0 (Zero.toOfNat0.{u1} R (CommMonoidWithZero.toZero.{u1} R (CommSemiring.toCommMonoidWithZero.{u1} R (CommRing.toCommSemiring.{u1} R (EuclideanDomain.toCommRing.{u1} R _inst_1))))))) -> (Eq.{succ u1} R (HDiv.hDiv.{u1, u1, u1} R R R (instHDiv.{u1} R (EuclideanDomain.instDiv.{u1} R _inst_1)) a a) (OfNat.ofNat.{u1} R 1 (One.toOfNat1.{u1} R (NonAssocRing.toOne.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R (EuclideanDomain.toCommRing.{u1} R _inst_1)))))))
Case conversion may be inaccurate. Consider using '#align euclidean_domain.div_self EuclideanDomain.div_selfₓ'. -/
@[simp]
theorem div_self {a : R} (a0 : a ≠ 0) : a / a = 1 := by
  simpa only [one_mul] using mul_div_cancel 1 a0
#align euclidean_domain.div_self EuclideanDomain.div_self

/- warning: euclidean_domain.eq_div_of_mul_eq_left -> EuclideanDomain.eq_div_of_mul_eq_left is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : EuclideanDomain.{u1} R] {a : R} {b : R} {c : R}, (Ne.{succ u1} R b (OfNat.ofNat.{u1} R 0 (OfNat.mk.{u1} R 0 (Zero.zero.{u1} R (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R (EuclideanDomain.toCommRing.{u1} R _inst_1))))))))))) -> (Eq.{succ u1} R (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (Distrib.toHasMul.{u1} R (Ring.toDistrib.{u1} R (CommRing.toRing.{u1} R (EuclideanDomain.toCommRing.{u1} R _inst_1))))) a b) c) -> (Eq.{succ u1} R a (HDiv.hDiv.{u1, u1, u1} R R R (instHDiv.{u1} R (EuclideanDomain.hasDiv.{u1} R _inst_1)) c b))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : EuclideanDomain.{u1} R] {a : R} {b : R} {c : R}, (Ne.{succ u1} R b (OfNat.ofNat.{u1} R 0 (Zero.toOfNat0.{u1} R (CommMonoidWithZero.toZero.{u1} R (CommSemiring.toCommMonoidWithZero.{u1} R (CommRing.toCommSemiring.{u1} R (EuclideanDomain.toCommRing.{u1} R _inst_1))))))) -> (Eq.{succ u1} R (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (NonUnitalNonAssocRing.toMul.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R (EuclideanDomain.toCommRing.{u1} R _inst_1)))))) a b) c) -> (Eq.{succ u1} R a (HDiv.hDiv.{u1, u1, u1} R R R (instHDiv.{u1} R (EuclideanDomain.instDiv.{u1} R _inst_1)) c b))
Case conversion may be inaccurate. Consider using '#align euclidean_domain.eq_div_of_mul_eq_left EuclideanDomain.eq_div_of_mul_eq_leftₓ'. -/
theorem eq_div_of_mul_eq_left {a b c : R} (hb : b ≠ 0) (h : a * b = c) : a = c / b := by
  rw [← h, mul_div_cancel _ hb]
#align euclidean_domain.eq_div_of_mul_eq_left EuclideanDomain.eq_div_of_mul_eq_left

/- warning: euclidean_domain.eq_div_of_mul_eq_right -> EuclideanDomain.eq_div_of_mul_eq_right is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : EuclideanDomain.{u1} R] {a : R} {b : R} {c : R}, (Ne.{succ u1} R a (OfNat.ofNat.{u1} R 0 (OfNat.mk.{u1} R 0 (Zero.zero.{u1} R (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R (EuclideanDomain.toCommRing.{u1} R _inst_1))))))))))) -> (Eq.{succ u1} R (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (Distrib.toHasMul.{u1} R (Ring.toDistrib.{u1} R (CommRing.toRing.{u1} R (EuclideanDomain.toCommRing.{u1} R _inst_1))))) a b) c) -> (Eq.{succ u1} R b (HDiv.hDiv.{u1, u1, u1} R R R (instHDiv.{u1} R (EuclideanDomain.hasDiv.{u1} R _inst_1)) c a))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : EuclideanDomain.{u1} R] {a : R} {b : R} {c : R}, (Ne.{succ u1} R a (OfNat.ofNat.{u1} R 0 (Zero.toOfNat0.{u1} R (CommMonoidWithZero.toZero.{u1} R (CommSemiring.toCommMonoidWithZero.{u1} R (CommRing.toCommSemiring.{u1} R (EuclideanDomain.toCommRing.{u1} R _inst_1))))))) -> (Eq.{succ u1} R (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (NonUnitalNonAssocRing.toMul.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R (EuclideanDomain.toCommRing.{u1} R _inst_1)))))) a b) c) -> (Eq.{succ u1} R b (HDiv.hDiv.{u1, u1, u1} R R R (instHDiv.{u1} R (EuclideanDomain.instDiv.{u1} R _inst_1)) c a))
Case conversion may be inaccurate. Consider using '#align euclidean_domain.eq_div_of_mul_eq_right EuclideanDomain.eq_div_of_mul_eq_rightₓ'. -/
theorem eq_div_of_mul_eq_right {a b c : R} (ha : a ≠ 0) (h : a * b = c) : b = c / a := by
  rw [← h, mul_div_cancel_left _ ha]
#align euclidean_domain.eq_div_of_mul_eq_right EuclideanDomain.eq_div_of_mul_eq_right

/- warning: euclidean_domain.mul_div_assoc -> EuclideanDomain.mul_div_assoc is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : EuclideanDomain.{u1} R] (x : R) {y : R} {z : R}, (Dvd.Dvd.{u1} R (semigroupDvd.{u1} R (SemigroupWithZero.toSemigroup.{u1} R (NonUnitalSemiring.toSemigroupWithZero.{u1} R (NonUnitalRing.toNonUnitalSemiring.{u1} R (NonUnitalCommRing.toNonUnitalRing.{u1} R (CommRing.toNonUnitalCommRing.{u1} R (EuclideanDomain.toCommRing.{u1} R _inst_1))))))) z y) -> (Eq.{succ u1} R (HDiv.hDiv.{u1, u1, u1} R R R (instHDiv.{u1} R (EuclideanDomain.hasDiv.{u1} R _inst_1)) (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (Distrib.toHasMul.{u1} R (Ring.toDistrib.{u1} R (CommRing.toRing.{u1} R (EuclideanDomain.toCommRing.{u1} R _inst_1))))) x y) z) (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (Distrib.toHasMul.{u1} R (Ring.toDistrib.{u1} R (CommRing.toRing.{u1} R (EuclideanDomain.toCommRing.{u1} R _inst_1))))) x (HDiv.hDiv.{u1, u1, u1} R R R (instHDiv.{u1} R (EuclideanDomain.hasDiv.{u1} R _inst_1)) y z)))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : EuclideanDomain.{u1} R] (x : R) {y : R} {z : R}, (Dvd.dvd.{u1} R (semigroupDvd.{u1} R (SemigroupWithZero.toSemigroup.{u1} R (NonUnitalSemiring.toSemigroupWithZero.{u1} R (NonUnitalRing.toNonUnitalSemiring.{u1} R (NonUnitalCommRing.toNonUnitalRing.{u1} R (CommRing.toNonUnitalCommRing.{u1} R (EuclideanDomain.toCommRing.{u1} R _inst_1))))))) z y) -> (Eq.{succ u1} R (HDiv.hDiv.{u1, u1, u1} R R R (instHDiv.{u1} R (EuclideanDomain.instDiv.{u1} R _inst_1)) (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (NonUnitalNonAssocRing.toMul.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R (EuclideanDomain.toCommRing.{u1} R _inst_1)))))) x y) z) (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (NonUnitalNonAssocRing.toMul.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R (EuclideanDomain.toCommRing.{u1} R _inst_1)))))) x (HDiv.hDiv.{u1, u1, u1} R R R (instHDiv.{u1} R (EuclideanDomain.instDiv.{u1} R _inst_1)) y z)))
Case conversion may be inaccurate. Consider using '#align euclidean_domain.mul_div_assoc EuclideanDomain.mul_div_assocₓ'. -/
theorem mul_div_assoc (x : R) {y z : R} (h : z ∣ y) : x * y / z = x * (y / z) := by
  classical
    by_cases hz : z = 0
    · subst hz
      rw [div_zero, div_zero, mul_zero]
    rcases h with ⟨p, rfl⟩
    rw [mul_div_cancel_left _ hz, mul_left_comm, mul_div_cancel_left _ hz]
#align euclidean_domain.mul_div_assoc EuclideanDomain.mul_div_assoc

#print EuclideanDomain.div_one /-
-- This generalizes `int.div_one`, see note [simp-normal form]
@[simp]
theorem div_one (p : R) : p / 1 = p :=
  (EuclideanDomain.eq_div_of_mul_eq_left (one_ne_zero' R) (mul_one p)).symm
#align euclidean_domain.div_one EuclideanDomain.div_one
-/

#print EuclideanDomain.div_dvd_of_dvd /-
theorem div_dvd_of_dvd {p q : R} (hpq : q ∣ p) : p / q ∣ p :=
  by
  by_cases hq : q = 0
  · rw [hq, zero_dvd_iff] at hpq
    rw [hpq]
    exact dvd_zero _
  use q
  rw [mul_comm, ← EuclideanDomain.mul_div_assoc _ hpq, mul_comm,
    EuclideanDomain.mul_div_cancel _ hq]
#align euclidean_domain.div_dvd_of_dvd EuclideanDomain.div_dvd_of_dvd
-/

/- warning: euclidean_domain.dvd_div_of_mul_dvd -> EuclideanDomain.dvd_div_of_mul_dvd is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : EuclideanDomain.{u1} R] {a : R} {b : R} {c : R}, (Dvd.Dvd.{u1} R (semigroupDvd.{u1} R (SemigroupWithZero.toSemigroup.{u1} R (NonUnitalSemiring.toSemigroupWithZero.{u1} R (NonUnitalRing.toNonUnitalSemiring.{u1} R (NonUnitalCommRing.toNonUnitalRing.{u1} R (CommRing.toNonUnitalCommRing.{u1} R (EuclideanDomain.toCommRing.{u1} R _inst_1))))))) (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (Distrib.toHasMul.{u1} R (Ring.toDistrib.{u1} R (CommRing.toRing.{u1} R (EuclideanDomain.toCommRing.{u1} R _inst_1))))) a b) c) -> (Dvd.Dvd.{u1} R (semigroupDvd.{u1} R (SemigroupWithZero.toSemigroup.{u1} R (NonUnitalSemiring.toSemigroupWithZero.{u1} R (NonUnitalRing.toNonUnitalSemiring.{u1} R (NonUnitalCommRing.toNonUnitalRing.{u1} R (CommRing.toNonUnitalCommRing.{u1} R (EuclideanDomain.toCommRing.{u1} R _inst_1))))))) b (HDiv.hDiv.{u1, u1, u1} R R R (instHDiv.{u1} R (EuclideanDomain.hasDiv.{u1} R _inst_1)) c a))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : EuclideanDomain.{u1} R] {a : R} {b : R} {c : R}, (Dvd.dvd.{u1} R (semigroupDvd.{u1} R (SemigroupWithZero.toSemigroup.{u1} R (NonUnitalSemiring.toSemigroupWithZero.{u1} R (NonUnitalRing.toNonUnitalSemiring.{u1} R (NonUnitalCommRing.toNonUnitalRing.{u1} R (CommRing.toNonUnitalCommRing.{u1} R (EuclideanDomain.toCommRing.{u1} R _inst_1))))))) (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (NonUnitalNonAssocRing.toMul.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R (EuclideanDomain.toCommRing.{u1} R _inst_1)))))) a b) c) -> (Dvd.dvd.{u1} R (semigroupDvd.{u1} R (SemigroupWithZero.toSemigroup.{u1} R (NonUnitalSemiring.toSemigroupWithZero.{u1} R (NonUnitalRing.toNonUnitalSemiring.{u1} R (NonUnitalCommRing.toNonUnitalRing.{u1} R (CommRing.toNonUnitalCommRing.{u1} R (EuclideanDomain.toCommRing.{u1} R _inst_1))))))) b (HDiv.hDiv.{u1, u1, u1} R R R (instHDiv.{u1} R (EuclideanDomain.instDiv.{u1} R _inst_1)) c a))
Case conversion may be inaccurate. Consider using '#align euclidean_domain.dvd_div_of_mul_dvd EuclideanDomain.dvd_div_of_mul_dvdₓ'. -/
theorem dvd_div_of_mul_dvd {a b c : R} (h : a * b ∣ c) : b ∣ c / a :=
  by
  rcases eq_or_ne a 0 with (rfl | ha)
  · simp only [div_zero, dvd_zero]
  rcases h with ⟨d, rfl⟩
  refine' ⟨d, _⟩
  rw [mul_assoc, mul_div_cancel_left _ ha]
#align euclidean_domain.dvd_div_of_mul_dvd EuclideanDomain.dvd_div_of_mul_dvd

section Gcd

variable [DecidableEq R]

/- warning: euclidean_domain.gcd_zero_right -> EuclideanDomain.gcd_zero_right is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : EuclideanDomain.{u1} R] [_inst_2 : DecidableEq.{succ u1} R] (a : R), Eq.{succ u1} R (EuclideanDomain.gcd.{u1} R _inst_1 (fun (a : R) (b : R) => _inst_2 a b) a (OfNat.ofNat.{u1} R 0 (OfNat.mk.{u1} R 0 (Zero.zero.{u1} R (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R (EuclideanDomain.toCommRing.{u1} R _inst_1))))))))))) a
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : EuclideanDomain.{u1} R] [_inst_2 : DecidableEq.{succ u1} R] (a : R), Eq.{succ u1} R (EuclideanDomain.gcd.{u1} R _inst_1 (fun (a : R) (b : R) => _inst_2 a b) a (OfNat.ofNat.{u1} R 0 (Zero.toOfNat0.{u1} R (CommMonoidWithZero.toZero.{u1} R (CommSemiring.toCommMonoidWithZero.{u1} R (CommRing.toCommSemiring.{u1} R (EuclideanDomain.toCommRing.{u1} R _inst_1))))))) a
Case conversion may be inaccurate. Consider using '#align euclidean_domain.gcd_zero_right EuclideanDomain.gcd_zero_rightₓ'. -/
@[simp]
theorem gcd_zero_right (a : R) : gcd a 0 = a :=
  by
  rw [gcd]
  split_ifs <;> simp only [h, zero_mod, gcd_zero_left]
#align euclidean_domain.gcd_zero_right EuclideanDomain.gcd_zero_right

#print EuclideanDomain.gcd_val /-
theorem gcd_val (a b : R) : gcd a b = gcd (b % a) a :=
  by
  rw [gcd]
  split_ifs <;> [simp only [h, mod_zero, gcd_zero_right], rfl]
#align euclidean_domain.gcd_val EuclideanDomain.gcd_val
-/

#print EuclideanDomain.gcd_dvd /-
theorem gcd_dvd (a b : R) : gcd a b ∣ a ∧ gcd a b ∣ b :=
  GCD.induction a b
    (fun b => by
      rw [gcd_zero_left]
      exact ⟨dvd_zero _, dvd_rfl⟩)
    fun a b aneq ⟨IH₁, IH₂⟩ => by
    rw [gcd_val]
    exact ⟨IH₂, (dvd_mod_iff IH₂).1 IH₁⟩
#align euclidean_domain.gcd_dvd EuclideanDomain.gcd_dvd
-/

#print EuclideanDomain.gcd_dvd_left /-
theorem gcd_dvd_left (a b : R) : gcd a b ∣ a :=
  (gcd_dvd a b).left
#align euclidean_domain.gcd_dvd_left EuclideanDomain.gcd_dvd_left
-/

#print EuclideanDomain.gcd_dvd_right /-
theorem gcd_dvd_right (a b : R) : gcd a b ∣ b :=
  (gcd_dvd a b).right
#align euclidean_domain.gcd_dvd_right EuclideanDomain.gcd_dvd_right
-/

/- warning: euclidean_domain.gcd_eq_zero_iff -> EuclideanDomain.gcd_eq_zero_iff is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : EuclideanDomain.{u1} R] [_inst_2 : DecidableEq.{succ u1} R] {a : R} {b : R}, Iff (Eq.{succ u1} R (EuclideanDomain.gcd.{u1} R _inst_1 (fun (a : R) (b : R) => _inst_2 a b) a b) (OfNat.ofNat.{u1} R 0 (OfNat.mk.{u1} R 0 (Zero.zero.{u1} R (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R (EuclideanDomain.toCommRing.{u1} R _inst_1))))))))))) (And (Eq.{succ u1} R a (OfNat.ofNat.{u1} R 0 (OfNat.mk.{u1} R 0 (Zero.zero.{u1} R (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R (EuclideanDomain.toCommRing.{u1} R _inst_1))))))))))) (Eq.{succ u1} R b (OfNat.ofNat.{u1} R 0 (OfNat.mk.{u1} R 0 (Zero.zero.{u1} R (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R (EuclideanDomain.toCommRing.{u1} R _inst_1))))))))))))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : EuclideanDomain.{u1} R] [_inst_2 : DecidableEq.{succ u1} R] {a : R} {b : R}, Iff (Eq.{succ u1} R (EuclideanDomain.gcd.{u1} R _inst_1 (fun (a : R) (b : R) => _inst_2 a b) a b) (OfNat.ofNat.{u1} R 0 (Zero.toOfNat0.{u1} R (CommMonoidWithZero.toZero.{u1} R (CommSemiring.toCommMonoidWithZero.{u1} R (CommRing.toCommSemiring.{u1} R (EuclideanDomain.toCommRing.{u1} R _inst_1))))))) (And (Eq.{succ u1} R a (OfNat.ofNat.{u1} R 0 (Zero.toOfNat0.{u1} R (CommMonoidWithZero.toZero.{u1} R (CommSemiring.toCommMonoidWithZero.{u1} R (CommRing.toCommSemiring.{u1} R (EuclideanDomain.toCommRing.{u1} R _inst_1))))))) (Eq.{succ u1} R b (OfNat.ofNat.{u1} R 0 (Zero.toOfNat0.{u1} R (CommMonoidWithZero.toZero.{u1} R (CommSemiring.toCommMonoidWithZero.{u1} R (CommRing.toCommSemiring.{u1} R (EuclideanDomain.toCommRing.{u1} R _inst_1))))))))
Case conversion may be inaccurate. Consider using '#align euclidean_domain.gcd_eq_zero_iff EuclideanDomain.gcd_eq_zero_iffₓ'. -/
protected theorem gcd_eq_zero_iff {a b : R} : gcd a b = 0 ↔ a = 0 ∧ b = 0 :=
  ⟨fun h => by simpa [h] using gcd_dvd a b,
    by
    rintro ⟨rfl, rfl⟩
    exact gcd_zero_right _⟩
#align euclidean_domain.gcd_eq_zero_iff EuclideanDomain.gcd_eq_zero_iff

#print EuclideanDomain.dvd_gcd /-
theorem dvd_gcd {a b c : R} : c ∣ a → c ∣ b → c ∣ gcd a b :=
  GCD.induction a b (fun _ _ H => by simpa only [gcd_zero_left] using H) fun a b a0 IH ca cb =>
    by
    rw [gcd_val]
    exact IH ((dvd_mod_iff ca).2 cb) ca
#align euclidean_domain.dvd_gcd EuclideanDomain.dvd_gcd
-/

#print EuclideanDomain.gcd_eq_left /-
theorem gcd_eq_left {a b : R} : gcd a b = a ↔ a ∣ b :=
  ⟨fun h => by
    rw [← h]
    apply gcd_dvd_right, fun h => by rw [gcd_val, mod_eq_zero.2 h, gcd_zero_left]⟩
#align euclidean_domain.gcd_eq_left EuclideanDomain.gcd_eq_left
-/

#print EuclideanDomain.gcd_one_left /-
@[simp]
theorem gcd_one_left (a : R) : gcd 1 a = 1 :=
  gcd_eq_left.2 (one_dvd _)
#align euclidean_domain.gcd_one_left EuclideanDomain.gcd_one_left
-/

#print EuclideanDomain.gcd_self /-
@[simp]
theorem gcd_self (a : R) : gcd a a = a :=
  gcd_eq_left.2 dvd_rfl
#align euclidean_domain.gcd_self EuclideanDomain.gcd_self
-/

#print EuclideanDomain.xgcdAux_fst /-
@[simp]
theorem xgcdAux_fst (x y : R) : ∀ s t s' t', (xgcdAux x s t y s' t').1 = gcd x y :=
  GCD.induction x y
    (by
      intros
      rw [xgcd_zero_left, gcd_zero_left])
    fun x y h IH s t s' t' => by
    simp only [xgcd_aux_rec h, if_neg h, IH]
    rw [← gcd_val]
#align euclidean_domain.xgcd_aux_fst EuclideanDomain.xgcdAux_fst
-/

/- warning: euclidean_domain.xgcd_aux_val -> EuclideanDomain.xgcdAux_val is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : EuclideanDomain.{u1} R] [_inst_2 : DecidableEq.{succ u1} R] (x : R) (y : R), Eq.{succ u1} (Prod.{u1, u1} R (Prod.{u1, u1} R R)) (EuclideanDomain.xgcdAux.{u1} R _inst_1 (fun (a : R) (b : R) => _inst_2 a b) x (OfNat.ofNat.{u1} R 1 (OfNat.mk.{u1} R 1 (One.one.{u1} R (AddMonoidWithOne.toOne.{u1} R (AddGroupWithOne.toAddMonoidWithOne.{u1} R (NonAssocRing.toAddGroupWithOne.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R (EuclideanDomain.toCommRing.{u1} R _inst_1))))))))) (OfNat.ofNat.{u1} R 0 (OfNat.mk.{u1} R 0 (Zero.zero.{u1} R (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R (EuclideanDomain.toCommRing.{u1} R _inst_1)))))))))) y (OfNat.ofNat.{u1} R 0 (OfNat.mk.{u1} R 0 (Zero.zero.{u1} R (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R (EuclideanDomain.toCommRing.{u1} R _inst_1)))))))))) (OfNat.ofNat.{u1} R 1 (OfNat.mk.{u1} R 1 (One.one.{u1} R (AddMonoidWithOne.toOne.{u1} R (AddGroupWithOne.toAddMonoidWithOne.{u1} R (NonAssocRing.toAddGroupWithOne.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R (EuclideanDomain.toCommRing.{u1} R _inst_1)))))))))) (Prod.mk.{u1, u1} R (Prod.{u1, u1} R R) (EuclideanDomain.gcd.{u1} R _inst_1 (fun (a : R) (b : R) => _inst_2 a b) x y) (EuclideanDomain.xgcd.{u1} R _inst_1 (fun (a : R) (b : R) => _inst_2 a b) x y))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : EuclideanDomain.{u1} R] [_inst_2 : DecidableEq.{succ u1} R] (x : R) (y : R), Eq.{succ u1} (Prod.{u1, u1} R (Prod.{u1, u1} R R)) (EuclideanDomain.xgcdAux.{u1} R _inst_1 (fun (a : R) (b : R) => _inst_2 a b) x (OfNat.ofNat.{u1} R 1 (One.toOfNat1.{u1} R (NonAssocRing.toOne.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R (EuclideanDomain.toCommRing.{u1} R _inst_1)))))) (OfNat.ofNat.{u1} R 0 (Zero.toOfNat0.{u1} R (CommMonoidWithZero.toZero.{u1} R (CommSemiring.toCommMonoidWithZero.{u1} R (CommRing.toCommSemiring.{u1} R (EuclideanDomain.toCommRing.{u1} R _inst_1)))))) y (OfNat.ofNat.{u1} R 0 (Zero.toOfNat0.{u1} R (CommMonoidWithZero.toZero.{u1} R (CommSemiring.toCommMonoidWithZero.{u1} R (CommRing.toCommSemiring.{u1} R (EuclideanDomain.toCommRing.{u1} R _inst_1)))))) (OfNat.ofNat.{u1} R 1 (One.toOfNat1.{u1} R (NonAssocRing.toOne.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R (EuclideanDomain.toCommRing.{u1} R _inst_1))))))) (Prod.mk.{u1, u1} R (Prod.{u1, u1} R R) (EuclideanDomain.gcd.{u1} R _inst_1 (fun (a : R) (b : R) => _inst_2 a b) x y) (EuclideanDomain.xgcd.{u1} R _inst_1 (fun (a : R) (b : R) => _inst_2 a b) x y))
Case conversion may be inaccurate. Consider using '#align euclidean_domain.xgcd_aux_val EuclideanDomain.xgcdAux_valₓ'. -/
theorem xgcdAux_val (x y : R) : xgcdAux x 1 0 y 0 1 = (gcd x y, xgcd x y) := by
  rw [xgcd, ← xgcd_aux_fst x y 1 0 0 1, Prod.mk.eta]
#align euclidean_domain.xgcd_aux_val EuclideanDomain.xgcdAux_val

private def P (a b : R) : R × R × R → Prop
  | (r, s, t) => (r : R) = a * s + b * t
#align euclidean_domain.P euclidean_domain.P

#print EuclideanDomain.xgcdAux_P /-
theorem xgcdAux_P (a b : R) {r r' : R} :
    ∀ {s t s' t'}, P a b (r, s, t) → P a b (r', s', t') → P a b (xgcdAux r s t r' s' t') :=
  GCD.induction r r'
    (by
      intros
      simpa only [xgcd_zero_left] )
    fun x y h IH s t s' t' p p' => by
    rw [xgcd_aux_rec h]; refine' IH _ p; unfold P at p p'⊢
    rw [mul_sub, mul_sub, add_sub, sub_add_eq_add_sub, ← p', sub_sub, mul_comm _ s, ← mul_assoc,
      mul_comm _ t, ← mul_assoc, ← add_mul, ← p, mod_eq_sub_mul_div]
#align euclidean_domain.xgcd_aux_P EuclideanDomain.xgcdAux_P
-/

/- warning: euclidean_domain.gcd_eq_gcd_ab -> EuclideanDomain.gcd_eq_gcd_ab is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : EuclideanDomain.{u1} R] [_inst_2 : DecidableEq.{succ u1} R] (a : R) (b : R), Eq.{succ u1} R (EuclideanDomain.gcd.{u1} R _inst_1 (fun (a : R) (b : R) => _inst_2 a b) a b) (HAdd.hAdd.{u1, u1, u1} R R R (instHAdd.{u1} R (Distrib.toHasAdd.{u1} R (Ring.toDistrib.{u1} R (CommRing.toRing.{u1} R (EuclideanDomain.toCommRing.{u1} R _inst_1))))) (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (Distrib.toHasMul.{u1} R (Ring.toDistrib.{u1} R (CommRing.toRing.{u1} R (EuclideanDomain.toCommRing.{u1} R _inst_1))))) a (EuclideanDomain.gcdA.{u1} R _inst_1 (fun (a : R) (b : R) => _inst_2 a b) a b)) (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (Distrib.toHasMul.{u1} R (Ring.toDistrib.{u1} R (CommRing.toRing.{u1} R (EuclideanDomain.toCommRing.{u1} R _inst_1))))) b (EuclideanDomain.gcdB.{u1} R _inst_1 (fun (a : R) (b : R) => _inst_2 a b) a b)))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : EuclideanDomain.{u1} R] [_inst_2 : DecidableEq.{succ u1} R] (a : R) (b : R), Eq.{succ u1} R (EuclideanDomain.gcd.{u1} R _inst_1 (fun (a : R) (b : R) => _inst_2 a b) a b) (HAdd.hAdd.{u1, u1, u1} R R R (instHAdd.{u1} R (Distrib.toAdd.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R (EuclideanDomain.toCommRing.{u1} R _inst_1)))))))) (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (NonUnitalNonAssocRing.toMul.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R (EuclideanDomain.toCommRing.{u1} R _inst_1)))))) a (EuclideanDomain.gcdA.{u1} R _inst_1 (fun (a : R) (b : R) => _inst_2 a b) a b)) (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (NonUnitalNonAssocRing.toMul.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R (EuclideanDomain.toCommRing.{u1} R _inst_1)))))) b (EuclideanDomain.gcdB.{u1} R _inst_1 (fun (a : R) (b : R) => _inst_2 a b) a b)))
Case conversion may be inaccurate. Consider using '#align euclidean_domain.gcd_eq_gcd_ab EuclideanDomain.gcd_eq_gcd_abₓ'. -/
/-- An explicit version of **Bézout's lemma** for Euclidean domains. -/
theorem gcd_eq_gcd_ab (a b : R) : (gcd a b : R) = a * gcdA a b + b * gcdB a b :=
  by
  have :=
    @xgcd_aux_P _ _ _ a b a b 1 0 0 1 (by rw [P, mul_one, mul_zero, add_zero])
      (by rw [P, mul_one, mul_zero, zero_add])
  rwa [xgcd_aux_val, xgcd_val] at this
#align euclidean_domain.gcd_eq_gcd_ab EuclideanDomain.gcd_eq_gcd_ab

-- see Note [lower instance priority]
instance (priority := 70) (R : Type _) [e : EuclideanDomain R] : NoZeroDivisors R :=
  haveI := Classical.decEq R
  {
    eq_zero_or_eq_zero_of_mul_eq_zero := fun a b h =>
      or_iff_not_and_not.2 fun h0 => h0.1 <| by rw [← mul_div_cancel a h0.2, h, zero_div] }

-- see Note [lower instance priority]
instance (priority := 70) (R : Type _) [e : EuclideanDomain R] : IsDomain R :=
  { e, NoZeroDivisors.to_isDomain R with }

end Gcd

section Lcm

variable [DecidableEq R]

#print EuclideanDomain.dvd_lcm_left /-
theorem dvd_lcm_left (x y : R) : x ∣ lcm x y :=
  by_cases
    (fun hxy : gcd x y = 0 => by
      rw [lcm, hxy, div_zero]
      exact dvd_zero _)
    fun hxy =>
    let ⟨z, hz⟩ := (gcd_dvd x y).2
    ⟨z, Eq.symm <| eq_div_of_mul_eq_left hxy <| by rw [mul_right_comm, mul_assoc, ← hz]⟩
#align euclidean_domain.dvd_lcm_left EuclideanDomain.dvd_lcm_left
-/

#print EuclideanDomain.dvd_lcm_right /-
theorem dvd_lcm_right (x y : R) : y ∣ lcm x y :=
  by_cases
    (fun hxy : gcd x y = 0 => by
      rw [lcm, hxy, div_zero]
      exact dvd_zero _)
    fun hxy =>
    let ⟨z, hz⟩ := (gcd_dvd x y).1
    ⟨z, Eq.symm <| eq_div_of_mul_eq_right hxy <| by rw [← mul_assoc, mul_right_comm, ← hz]⟩
#align euclidean_domain.dvd_lcm_right EuclideanDomain.dvd_lcm_right
-/

#print EuclideanDomain.lcm_dvd /-
theorem lcm_dvd {x y z : R} (hxz : x ∣ z) (hyz : y ∣ z) : lcm x y ∣ z :=
  by
  rw [lcm]
  by_cases hxy : gcd x y = 0
  · rw [hxy, div_zero]
    rw [EuclideanDomain.gcd_eq_zero_iff] at hxy
    rwa [hxy.1] at hxz
  rcases gcd_dvd x y with ⟨⟨r, hr⟩, ⟨s, hs⟩⟩
  suffices x * y ∣ z * gcd x y by
    cases' this with p hp
    use p
    generalize gcd x y = g at hxy hs hp⊢
    subst hs
    rw [mul_left_comm, mul_div_cancel_left _ hxy, ← mul_left_inj' hxy, hp]
    rw [← mul_assoc]
    simp only [mul_right_comm]
  rw [gcd_eq_gcd_ab, mul_add]
  apply dvd_add
  · rw [mul_left_comm]
    exact mul_dvd_mul_left _ (hyz.mul_right _)
  · rw [mul_left_comm, mul_comm]
    exact mul_dvd_mul_left _ (hxz.mul_right _)
#align euclidean_domain.lcm_dvd EuclideanDomain.lcm_dvd
-/

#print EuclideanDomain.lcm_dvd_iff /-
@[simp]
theorem lcm_dvd_iff {x y z : R} : lcm x y ∣ z ↔ x ∣ z ∧ y ∣ z :=
  ⟨fun hz => ⟨(dvd_lcm_left _ _).trans hz, (dvd_lcm_right _ _).trans hz⟩, fun ⟨hxz, hyz⟩ =>
    lcm_dvd hxz hyz⟩
#align euclidean_domain.lcm_dvd_iff EuclideanDomain.lcm_dvd_iff
-/

/- warning: euclidean_domain.lcm_zero_left -> EuclideanDomain.lcm_zero_left is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : EuclideanDomain.{u1} R] [_inst_2 : DecidableEq.{succ u1} R] (x : R), Eq.{succ u1} R (EuclideanDomain.lcm.{u1} R _inst_1 (fun (a : R) (b : R) => _inst_2 a b) (OfNat.ofNat.{u1} R 0 (OfNat.mk.{u1} R 0 (Zero.zero.{u1} R (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R (EuclideanDomain.toCommRing.{u1} R _inst_1)))))))))) x) (OfNat.ofNat.{u1} R 0 (OfNat.mk.{u1} R 0 (Zero.zero.{u1} R (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R (EuclideanDomain.toCommRing.{u1} R _inst_1))))))))))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : EuclideanDomain.{u1} R] [_inst_2 : DecidableEq.{succ u1} R] (x : R), Eq.{succ u1} R (EuclideanDomain.lcm.{u1} R _inst_1 (fun (a : R) (b : R) => _inst_2 a b) (OfNat.ofNat.{u1} R 0 (Zero.toOfNat0.{u1} R (CommMonoidWithZero.toZero.{u1} R (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} R (IsDomain.toCancelCommMonoidWithZero.{u1} R (CommRing.toCommSemiring.{u1} R (EuclideanDomain.toCommRing.{u1} R _inst_1)) (EuclideanDomain.instIsDomainToSemiringToRingToCommRing.{u1} R _inst_1)))))) x) (OfNat.ofNat.{u1} R 0 (Zero.toOfNat0.{u1} R (CommMonoidWithZero.toZero.{u1} R (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} R (IsDomain.toCancelCommMonoidWithZero.{u1} R (CommRing.toCommSemiring.{u1} R (EuclideanDomain.toCommRing.{u1} R _inst_1)) (EuclideanDomain.instIsDomainToSemiringToRingToCommRing.{u1} R _inst_1))))))
Case conversion may be inaccurate. Consider using '#align euclidean_domain.lcm_zero_left EuclideanDomain.lcm_zero_leftₓ'. -/
@[simp]
theorem lcm_zero_left (x : R) : lcm 0 x = 0 := by rw [lcm, zero_mul, zero_div]
#align euclidean_domain.lcm_zero_left EuclideanDomain.lcm_zero_left

/- warning: euclidean_domain.lcm_zero_right -> EuclideanDomain.lcm_zero_right is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : EuclideanDomain.{u1} R] [_inst_2 : DecidableEq.{succ u1} R] (x : R), Eq.{succ u1} R (EuclideanDomain.lcm.{u1} R _inst_1 (fun (a : R) (b : R) => _inst_2 a b) x (OfNat.ofNat.{u1} R 0 (OfNat.mk.{u1} R 0 (Zero.zero.{u1} R (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R (EuclideanDomain.toCommRing.{u1} R _inst_1))))))))))) (OfNat.ofNat.{u1} R 0 (OfNat.mk.{u1} R 0 (Zero.zero.{u1} R (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R (EuclideanDomain.toCommRing.{u1} R _inst_1))))))))))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : EuclideanDomain.{u1} R] [_inst_2 : DecidableEq.{succ u1} R] (x : R), Eq.{succ u1} R (EuclideanDomain.lcm.{u1} R _inst_1 (fun (a : R) (b : R) => _inst_2 a b) x (OfNat.ofNat.{u1} R 0 (Zero.toOfNat0.{u1} R (CommMonoidWithZero.toZero.{u1} R (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} R (IsDomain.toCancelCommMonoidWithZero.{u1} R (CommRing.toCommSemiring.{u1} R (EuclideanDomain.toCommRing.{u1} R _inst_1)) (EuclideanDomain.instIsDomainToSemiringToRingToCommRing.{u1} R _inst_1))))))) (OfNat.ofNat.{u1} R 0 (Zero.toOfNat0.{u1} R (CommMonoidWithZero.toZero.{u1} R (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} R (IsDomain.toCancelCommMonoidWithZero.{u1} R (CommRing.toCommSemiring.{u1} R (EuclideanDomain.toCommRing.{u1} R _inst_1)) (EuclideanDomain.instIsDomainToSemiringToRingToCommRing.{u1} R _inst_1))))))
Case conversion may be inaccurate. Consider using '#align euclidean_domain.lcm_zero_right EuclideanDomain.lcm_zero_rightₓ'. -/
@[simp]
theorem lcm_zero_right (x : R) : lcm x 0 = 0 := by rw [lcm, mul_zero, zero_div]
#align euclidean_domain.lcm_zero_right EuclideanDomain.lcm_zero_right

/- warning: euclidean_domain.lcm_eq_zero_iff -> EuclideanDomain.lcm_eq_zero_iff is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : EuclideanDomain.{u1} R] [_inst_2 : DecidableEq.{succ u1} R] {x : R} {y : R}, Iff (Eq.{succ u1} R (EuclideanDomain.lcm.{u1} R _inst_1 (fun (a : R) (b : R) => _inst_2 a b) x y) (OfNat.ofNat.{u1} R 0 (OfNat.mk.{u1} R 0 (Zero.zero.{u1} R (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R (EuclideanDomain.toCommRing.{u1} R _inst_1))))))))))) (Or (Eq.{succ u1} R x (OfNat.ofNat.{u1} R 0 (OfNat.mk.{u1} R 0 (Zero.zero.{u1} R (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R (EuclideanDomain.toCommRing.{u1} R _inst_1))))))))))) (Eq.{succ u1} R y (OfNat.ofNat.{u1} R 0 (OfNat.mk.{u1} R 0 (Zero.zero.{u1} R (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R (EuclideanDomain.toCommRing.{u1} R _inst_1))))))))))))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : EuclideanDomain.{u1} R] [_inst_2 : DecidableEq.{succ u1} R] {x : R} {y : R}, Iff (Eq.{succ u1} R (EuclideanDomain.lcm.{u1} R _inst_1 (fun (a : R) (b : R) => _inst_2 a b) x y) (OfNat.ofNat.{u1} R 0 (Zero.toOfNat0.{u1} R (CommMonoidWithZero.toZero.{u1} R (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} R (IsDomain.toCancelCommMonoidWithZero.{u1} R (CommRing.toCommSemiring.{u1} R (EuclideanDomain.toCommRing.{u1} R _inst_1)) (EuclideanDomain.instIsDomainToSemiringToRingToCommRing.{u1} R _inst_1))))))) (Or (Eq.{succ u1} R x (OfNat.ofNat.{u1} R 0 (Zero.toOfNat0.{u1} R (CommMonoidWithZero.toZero.{u1} R (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} R (IsDomain.toCancelCommMonoidWithZero.{u1} R (CommRing.toCommSemiring.{u1} R (EuclideanDomain.toCommRing.{u1} R _inst_1)) (EuclideanDomain.instIsDomainToSemiringToRingToCommRing.{u1} R _inst_1))))))) (Eq.{succ u1} R y (OfNat.ofNat.{u1} R 0 (Zero.toOfNat0.{u1} R (CommMonoidWithZero.toZero.{u1} R (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} R (IsDomain.toCancelCommMonoidWithZero.{u1} R (CommRing.toCommSemiring.{u1} R (EuclideanDomain.toCommRing.{u1} R _inst_1)) (EuclideanDomain.instIsDomainToSemiringToRingToCommRing.{u1} R _inst_1))))))))
Case conversion may be inaccurate. Consider using '#align euclidean_domain.lcm_eq_zero_iff EuclideanDomain.lcm_eq_zero_iffₓ'. -/
@[simp]
theorem lcm_eq_zero_iff {x y : R} : lcm x y = 0 ↔ x = 0 ∨ y = 0 :=
  by
  constructor
  · intro hxy
    rw [lcm, mul_div_assoc _ (gcd_dvd_right _ _), mul_eq_zero] at hxy
    apply or_of_or_of_imp_right hxy
    intro hy
    by_cases hgxy : gcd x y = 0
    · rw [EuclideanDomain.gcd_eq_zero_iff] at hgxy
      exact hgxy.2
    · rcases gcd_dvd x y with ⟨⟨r, hr⟩, ⟨s, hs⟩⟩
      generalize gcd x y = g at hr hs hy hgxy⊢
      subst hs
      rw [mul_div_cancel_left _ hgxy] at hy
      rw [hy, mul_zero]
  rintro (hx | hy)
  · rw [hx, lcm_zero_left]
  · rw [hy, lcm_zero_right]
#align euclidean_domain.lcm_eq_zero_iff EuclideanDomain.lcm_eq_zero_iff

/- warning: euclidean_domain.gcd_mul_lcm -> EuclideanDomain.gcd_mul_lcm is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : EuclideanDomain.{u1} R] [_inst_2 : DecidableEq.{succ u1} R] (x : R) (y : R), Eq.{succ u1} R (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (Distrib.toHasMul.{u1} R (Ring.toDistrib.{u1} R (CommRing.toRing.{u1} R (EuclideanDomain.toCommRing.{u1} R _inst_1))))) (EuclideanDomain.gcd.{u1} R _inst_1 (fun (a : R) (b : R) => _inst_2 a b) x y) (EuclideanDomain.lcm.{u1} R _inst_1 (fun (a : R) (b : R) => _inst_2 a b) x y)) (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (Distrib.toHasMul.{u1} R (Ring.toDistrib.{u1} R (CommRing.toRing.{u1} R (EuclideanDomain.toCommRing.{u1} R _inst_1))))) x y)
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : EuclideanDomain.{u1} R] [_inst_2 : DecidableEq.{succ u1} R] (x : R) (y : R), Eq.{succ u1} R (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (NonUnitalNonAssocRing.toMul.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R (EuclideanDomain.toCommRing.{u1} R _inst_1)))))) (EuclideanDomain.gcd.{u1} R _inst_1 (fun (a : R) (b : R) => _inst_2 a b) x y) (EuclideanDomain.lcm.{u1} R _inst_1 (fun (a : R) (b : R) => _inst_2 a b) x y)) (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (NonUnitalNonAssocRing.toMul.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R (EuclideanDomain.toCommRing.{u1} R _inst_1)))))) x y)
Case conversion may be inaccurate. Consider using '#align euclidean_domain.gcd_mul_lcm EuclideanDomain.gcd_mul_lcmₓ'. -/
@[simp]
theorem gcd_mul_lcm (x y : R) : gcd x y * lcm x y = x * y :=
  by
  rw [lcm]; by_cases h : gcd x y = 0
  · rw [h, zero_mul]
    rw [EuclideanDomain.gcd_eq_zero_iff] at h
    rw [h.1, zero_mul]
  rcases gcd_dvd x y with ⟨⟨r, hr⟩, ⟨s, hs⟩⟩
  generalize gcd x y = g at h hr⊢; subst hr
  rw [mul_assoc, mul_div_cancel_left _ h]
#align euclidean_domain.gcd_mul_lcm EuclideanDomain.gcd_mul_lcm

end Lcm

section Div

/- warning: euclidean_domain.mul_div_mul_cancel -> EuclideanDomain.mul_div_mul_cancel is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : EuclideanDomain.{u1} R] {a : R} {b : R} {c : R}, (Ne.{succ u1} R a (OfNat.ofNat.{u1} R 0 (OfNat.mk.{u1} R 0 (Zero.zero.{u1} R (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R (EuclideanDomain.toCommRing.{u1} R _inst_1))))))))))) -> (Dvd.Dvd.{u1} R (semigroupDvd.{u1} R (SemigroupWithZero.toSemigroup.{u1} R (NonUnitalSemiring.toSemigroupWithZero.{u1} R (NonUnitalRing.toNonUnitalSemiring.{u1} R (NonUnitalCommRing.toNonUnitalRing.{u1} R (CommRing.toNonUnitalCommRing.{u1} R (EuclideanDomain.toCommRing.{u1} R _inst_1))))))) c b) -> (Eq.{succ u1} R (HDiv.hDiv.{u1, u1, u1} R R R (instHDiv.{u1} R (EuclideanDomain.hasDiv.{u1} R _inst_1)) (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (Distrib.toHasMul.{u1} R (Ring.toDistrib.{u1} R (CommRing.toRing.{u1} R (EuclideanDomain.toCommRing.{u1} R _inst_1))))) a b) (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (Distrib.toHasMul.{u1} R (Ring.toDistrib.{u1} R (CommRing.toRing.{u1} R (EuclideanDomain.toCommRing.{u1} R _inst_1))))) a c)) (HDiv.hDiv.{u1, u1, u1} R R R (instHDiv.{u1} R (EuclideanDomain.hasDiv.{u1} R _inst_1)) b c))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : EuclideanDomain.{u1} R] {a : R} {b : R} {c : R}, (Ne.{succ u1} R a (OfNat.ofNat.{u1} R 0 (Zero.toOfNat0.{u1} R (CommMonoidWithZero.toZero.{u1} R (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} R (IsDomain.toCancelCommMonoidWithZero.{u1} R (CommRing.toCommSemiring.{u1} R (EuclideanDomain.toCommRing.{u1} R _inst_1)) (EuclideanDomain.instIsDomainToSemiringToRingToCommRing.{u1} R _inst_1))))))) -> (Dvd.dvd.{u1} R (semigroupDvd.{u1} R (SemigroupWithZero.toSemigroup.{u1} R (NonUnitalSemiring.toSemigroupWithZero.{u1} R (NonUnitalRing.toNonUnitalSemiring.{u1} R (NonUnitalCommRing.toNonUnitalRing.{u1} R (CommRing.toNonUnitalCommRing.{u1} R (EuclideanDomain.toCommRing.{u1} R _inst_1))))))) c b) -> (Eq.{succ u1} R (HDiv.hDiv.{u1, u1, u1} R R R (instHDiv.{u1} R (EuclideanDomain.instDiv.{u1} R _inst_1)) (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (NonUnitalNonAssocRing.toMul.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R (EuclideanDomain.toCommRing.{u1} R _inst_1)))))) a b) (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (NonUnitalNonAssocRing.toMul.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R (EuclideanDomain.toCommRing.{u1} R _inst_1)))))) a c)) (HDiv.hDiv.{u1, u1, u1} R R R (instHDiv.{u1} R (EuclideanDomain.instDiv.{u1} R _inst_1)) b c))
Case conversion may be inaccurate. Consider using '#align euclidean_domain.mul_div_mul_cancel EuclideanDomain.mul_div_mul_cancelₓ'. -/
theorem mul_div_mul_cancel {a b c : R} (ha : a ≠ 0) (hcb : c ∣ b) : a * b / (a * c) = b / c :=
  by
  by_cases hc : c = 0; · simp [hc]
  refine' eq_div_of_mul_eq_right hc (mul_left_cancel₀ ha _)
  rw [← mul_assoc, ← mul_div_assoc _ (mul_dvd_mul_left a hcb),
    mul_div_cancel_left _ (mul_ne_zero ha hc)]
#align euclidean_domain.mul_div_mul_cancel EuclideanDomain.mul_div_mul_cancel

/- warning: euclidean_domain.mul_div_mul_comm_of_dvd_dvd -> EuclideanDomain.mul_div_mul_comm_of_dvd_dvd is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : EuclideanDomain.{u1} R] {a : R} {b : R} {c : R} {d : R}, (Dvd.Dvd.{u1} R (semigroupDvd.{u1} R (SemigroupWithZero.toSemigroup.{u1} R (NonUnitalSemiring.toSemigroupWithZero.{u1} R (NonUnitalRing.toNonUnitalSemiring.{u1} R (NonUnitalCommRing.toNonUnitalRing.{u1} R (CommRing.toNonUnitalCommRing.{u1} R (EuclideanDomain.toCommRing.{u1} R _inst_1))))))) c a) -> (Dvd.Dvd.{u1} R (semigroupDvd.{u1} R (SemigroupWithZero.toSemigroup.{u1} R (NonUnitalSemiring.toSemigroupWithZero.{u1} R (NonUnitalRing.toNonUnitalSemiring.{u1} R (NonUnitalCommRing.toNonUnitalRing.{u1} R (CommRing.toNonUnitalCommRing.{u1} R (EuclideanDomain.toCommRing.{u1} R _inst_1))))))) d b) -> (Eq.{succ u1} R (HDiv.hDiv.{u1, u1, u1} R R R (instHDiv.{u1} R (EuclideanDomain.hasDiv.{u1} R _inst_1)) (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (Distrib.toHasMul.{u1} R (Ring.toDistrib.{u1} R (CommRing.toRing.{u1} R (EuclideanDomain.toCommRing.{u1} R _inst_1))))) a b) (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (Distrib.toHasMul.{u1} R (Ring.toDistrib.{u1} R (CommRing.toRing.{u1} R (EuclideanDomain.toCommRing.{u1} R _inst_1))))) c d)) (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (Distrib.toHasMul.{u1} R (Ring.toDistrib.{u1} R (CommRing.toRing.{u1} R (EuclideanDomain.toCommRing.{u1} R _inst_1))))) (HDiv.hDiv.{u1, u1, u1} R R R (instHDiv.{u1} R (EuclideanDomain.hasDiv.{u1} R _inst_1)) a c) (HDiv.hDiv.{u1, u1, u1} R R R (instHDiv.{u1} R (EuclideanDomain.hasDiv.{u1} R _inst_1)) b d)))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : EuclideanDomain.{u1} R] {a : R} {b : R} {c : R} {d : R}, (Dvd.dvd.{u1} R (semigroupDvd.{u1} R (SemigroupWithZero.toSemigroup.{u1} R (NonUnitalSemiring.toSemigroupWithZero.{u1} R (NonUnitalRing.toNonUnitalSemiring.{u1} R (NonUnitalCommRing.toNonUnitalRing.{u1} R (CommRing.toNonUnitalCommRing.{u1} R (EuclideanDomain.toCommRing.{u1} R _inst_1))))))) c a) -> (Dvd.dvd.{u1} R (semigroupDvd.{u1} R (SemigroupWithZero.toSemigroup.{u1} R (NonUnitalSemiring.toSemigroupWithZero.{u1} R (NonUnitalRing.toNonUnitalSemiring.{u1} R (NonUnitalCommRing.toNonUnitalRing.{u1} R (CommRing.toNonUnitalCommRing.{u1} R (EuclideanDomain.toCommRing.{u1} R _inst_1))))))) d b) -> (Eq.{succ u1} R (HDiv.hDiv.{u1, u1, u1} R R R (instHDiv.{u1} R (EuclideanDomain.instDiv.{u1} R _inst_1)) (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (NonUnitalNonAssocRing.toMul.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R (EuclideanDomain.toCommRing.{u1} R _inst_1)))))) a b) (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (NonUnitalNonAssocRing.toMul.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R (EuclideanDomain.toCommRing.{u1} R _inst_1)))))) c d)) (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (NonUnitalNonAssocRing.toMul.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R (EuclideanDomain.toCommRing.{u1} R _inst_1)))))) (HDiv.hDiv.{u1, u1, u1} R R R (instHDiv.{u1} R (EuclideanDomain.instDiv.{u1} R _inst_1)) a c) (HDiv.hDiv.{u1, u1, u1} R R R (instHDiv.{u1} R (EuclideanDomain.instDiv.{u1} R _inst_1)) b d)))
Case conversion may be inaccurate. Consider using '#align euclidean_domain.mul_div_mul_comm_of_dvd_dvd EuclideanDomain.mul_div_mul_comm_of_dvd_dvdₓ'. -/
theorem mul_div_mul_comm_of_dvd_dvd {a b c d : R} (hac : c ∣ a) (hbd : d ∣ b) :
    a * b / (c * d) = a / c * (b / d) :=
  by
  rcases eq_or_ne c 0 with (rfl | hc0); · simp
  rcases eq_or_ne d 0 with (rfl | hd0); · simp
  obtain ⟨k1, rfl⟩ := hac
  obtain ⟨k2, rfl⟩ := hbd
  rw [mul_div_cancel_left _ hc0, mul_div_cancel_left _ hd0, mul_mul_mul_comm,
    mul_div_cancel_left _ (mul_ne_zero hc0 hd0)]
#align euclidean_domain.mul_div_mul_comm_of_dvd_dvd EuclideanDomain.mul_div_mul_comm_of_dvd_dvd

end Div

end EuclideanDomain

