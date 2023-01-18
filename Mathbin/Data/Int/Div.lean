/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad

! This file was ported from Lean 3 source module data.int.div
! leanprover-community/mathlib commit 008205aa645b3f194c1da47025c5f110c8406eab
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Int.Dvd.Basic
import Mathbin.Data.Nat.Order.Lemmas
import Mathbin.Algebra.Ring.Regular

/-!
# Lemmas relating `/` in `ℤ` with the ordering.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.
-/


open Nat

namespace Int

/- warning: int.eq_mul_div_of_mul_eq_mul_of_dvd_left -> Int.eq_mul_div_of_mul_eq_mul_of_dvd_left is a dubious translation:
lean 3 declaration is
  forall {a : Int} {b : Int} {c : Int} {d : Int}, (Ne.{1} Int b (OfNat.ofNat.{0} Int 0 (OfNat.mk.{0} Int 0 (Zero.zero.{0} Int Int.hasZero)))) -> (Dvd.Dvd.{0} Int (semigroupDvd.{0} Int Int.semigroup) b c) -> (Eq.{1} Int (HMul.hMul.{0, 0, 0} Int Int Int (instHMul.{0} Int Int.hasMul) b a) (HMul.hMul.{0, 0, 0} Int Int Int (instHMul.{0} Int Int.hasMul) c d)) -> (Eq.{1} Int a (HMul.hMul.{0, 0, 0} Int Int Int (instHMul.{0} Int Int.hasMul) (HDiv.hDiv.{0, 0, 0} Int Int Int (instHDiv.{0} Int Int.hasDiv) c b) d))
but is expected to have type
  forall {a : Int} {b : Int} {c : Int} {d : Int}, (Ne.{1} Int b (OfNat.ofNat.{0} Int 0 (instOfNatInt 0))) -> (Dvd.dvd.{0} Int Int.instDvdInt b c) -> (Eq.{1} Int (HMul.hMul.{0, 0, 0} Int Int Int (instHMul.{0} Int Int.instMulInt) b a) (HMul.hMul.{0, 0, 0} Int Int Int (instHMul.{0} Int Int.instMulInt) c d)) -> (Eq.{1} Int a (HMul.hMul.{0, 0, 0} Int Int Int (instHMul.{0} Int Int.instMulInt) (HDiv.hDiv.{0, 0, 0} Int Int Int (instHDiv.{0} Int Int.instDivInt_1) c b) d))
Case conversion may be inaccurate. Consider using '#align int.eq_mul_div_of_mul_eq_mul_of_dvd_left Int.eq_mul_div_of_mul_eq_mul_of_dvd_leftₓ'. -/
theorem eq_mul_div_of_mul_eq_mul_of_dvd_left {a b c d : ℤ} (hb : b ≠ 0) (hbc : b ∣ c)
    (h : b * a = c * d) : a = c / b * d :=
  by
  cases' hbc with k hk
  subst hk
  rw [Int.mul_ediv_cancel_left _ hb]
  rw [mul_assoc] at h
  apply mul_left_cancel₀ hb h
#align int.eq_mul_div_of_mul_eq_mul_of_dvd_left Int.eq_mul_div_of_mul_eq_mul_of_dvd_left

/- warning: int.eq_zero_of_dvd_of_nat_abs_lt_nat_abs -> Int.eq_zero_of_dvd_of_natAbs_lt_natAbs is a dubious translation:
lean 3 declaration is
  forall {a : Int} {b : Int}, (Dvd.Dvd.{0} Int (semigroupDvd.{0} Int Int.semigroup) a b) -> (LT.lt.{0} Nat Nat.hasLt (Int.natAbs b) (Int.natAbs a)) -> (Eq.{1} Int b (OfNat.ofNat.{0} Int 0 (OfNat.mk.{0} Int 0 (Zero.zero.{0} Int Int.hasZero))))
but is expected to have type
  forall {a : Int} {b : Int}, (Dvd.dvd.{0} Int Int.instDvdInt a b) -> (LT.lt.{0} Nat instLTNat (Int.natAbs b) (Int.natAbs a)) -> (Eq.{1} Int b (OfNat.ofNat.{0} Int 0 (instOfNatInt 0)))
Case conversion may be inaccurate. Consider using '#align int.eq_zero_of_dvd_of_nat_abs_lt_nat_abs Int.eq_zero_of_dvd_of_natAbs_lt_natAbsₓ'. -/
/-- If an integer with larger absolute value divides an integer, it is
zero. -/
theorem eq_zero_of_dvd_of_natAbs_lt_natAbs {a b : ℤ} (w : a ∣ b) (h : natAbs b < natAbs a) :
    b = 0 := by
  rw [← nat_abs_dvd, ← dvd_nat_abs, coe_nat_dvd] at w
  rw [← nat_abs_eq_zero]
  exact eq_zero_of_dvd_of_lt w h
#align int.eq_zero_of_dvd_of_nat_abs_lt_nat_abs Int.eq_zero_of_dvd_of_natAbs_lt_natAbs

/- warning: int.eq_zero_of_dvd_of_nonneg_of_lt -> Int.eq_zero_of_dvd_of_nonneg_of_lt is a dubious translation:
lean 3 declaration is
  forall {a : Int} {b : Int}, (LE.le.{0} Int Int.hasLe (OfNat.ofNat.{0} Int 0 (OfNat.mk.{0} Int 0 (Zero.zero.{0} Int Int.hasZero))) a) -> (LT.lt.{0} Int Int.hasLt a b) -> (Dvd.Dvd.{0} Int (semigroupDvd.{0} Int Int.semigroup) b a) -> (Eq.{1} Int a (OfNat.ofNat.{0} Int 0 (OfNat.mk.{0} Int 0 (Zero.zero.{0} Int Int.hasZero))))
but is expected to have type
  forall {a : Int} {b : Int}, (LE.le.{0} Int Int.instLEInt (OfNat.ofNat.{0} Int 0 (instOfNatInt 0)) a) -> (LT.lt.{0} Int Int.instLTInt a b) -> (Dvd.dvd.{0} Int Int.instDvdInt b a) -> (Eq.{1} Int a (OfNat.ofNat.{0} Int 0 (instOfNatInt 0)))
Case conversion may be inaccurate. Consider using '#align int.eq_zero_of_dvd_of_nonneg_of_lt Int.eq_zero_of_dvd_of_nonneg_of_ltₓ'. -/
theorem eq_zero_of_dvd_of_nonneg_of_lt {a b : ℤ} (w₁ : 0 ≤ a) (w₂ : a < b) (h : b ∣ a) : a = 0 :=
  eq_zero_of_dvd_of_natAbs_lt_natAbs h (natAbs_lt_natAbs_of_nonneg_of_lt w₁ w₂)
#align int.eq_zero_of_dvd_of_nonneg_of_lt Int.eq_zero_of_dvd_of_nonneg_of_lt

#print Int.eq_of_mod_eq_of_natAbs_sub_lt_natAbs /-
/-- If two integers are congruent to a sufficiently large modulus,
they are equal. -/
theorem eq_of_mod_eq_of_natAbs_sub_lt_natAbs {a b c : ℤ} (h1 : a % b = c)
    (h2 : natAbs (a - c) < natAbs b) : a = c :=
  eq_of_sub_eq_zero (eq_zero_of_dvd_of_natAbs_lt_natAbs (dvd_sub_of_emod_eq h1) h2)
#align int.eq_of_mod_eq_of_nat_abs_sub_lt_nat_abs Int.eq_of_mod_eq_of_natAbs_sub_lt_natAbs
-/

#print Int.ofNat_add_negSucc_of_ge /-
theorem ofNat_add_negSucc_of_ge {m n : ℕ} (h : n.succ ≤ m) :
    ofNat m + -[n+1] = ofNat (m - n.succ) :=
  by
  change sub_nat_nat _ _ = _
  have h' : n.succ - m = 0
  apply tsub_eq_zero_iff_le.mpr h
  simp [*, sub_nat_nat]
#align int.of_nat_add_neg_succ_of_nat_of_ge Int.ofNat_add_negSucc_of_ge
-/

/- warning: int.nat_abs_le_of_dvd_ne_zero -> Int.natAbs_le_of_dvd_ne_zero is a dubious translation:
lean 3 declaration is
  forall {s : Int} {t : Int}, (Dvd.Dvd.{0} Int (semigroupDvd.{0} Int Int.semigroup) s t) -> (Ne.{1} Int t (OfNat.ofNat.{0} Int 0 (OfNat.mk.{0} Int 0 (Zero.zero.{0} Int Int.hasZero)))) -> (LE.le.{0} Nat Nat.hasLe (Int.natAbs s) (Int.natAbs t))
but is expected to have type
  forall {s : Int} {t : Int}, (Dvd.dvd.{0} Int Int.instDvdInt s t) -> (Ne.{1} Int t (OfNat.ofNat.{0} Int 0 (instOfNatInt 0))) -> (LE.le.{0} Nat instLENat (Int.natAbs s) (Int.natAbs t))
Case conversion may be inaccurate. Consider using '#align int.nat_abs_le_of_dvd_ne_zero Int.natAbs_le_of_dvd_ne_zeroₓ'. -/
theorem natAbs_le_of_dvd_ne_zero {s t : ℤ} (hst : s ∣ t) (ht : t ≠ 0) : natAbs s ≤ natAbs t :=
  not_lt.mp (mt (eq_zero_of_dvd_of_natAbs_lt_natAbs hst) ht)
#align int.nat_abs_le_of_dvd_ne_zero Int.natAbs_le_of_dvd_ne_zero

end Int

