/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad

! This file was ported from Lean 3 source module data.int.lemmas
! leanprover-community/mathlib commit 4c19a16e4b705bf135cf9a80ac18fcc99c438514
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Set.Function
import Mathbin.Data.Int.Order.Lemmas
import Mathbin.Data.Int.Bitwise
import Mathbin.Data.Nat.Cast.Basic
import Mathbin.Data.Nat.Order.Lemmas

/-!
# Miscellaneous lemmas about the integers

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file contains lemmas about integers, which require further imports than
`data.int.basic` or `data.int.order`.

-/


open Nat

namespace Int

#print Int.le_coe_nat_sub /-
theorem le_coe_nat_sub (m n : ℕ) : (m - n : ℤ) ≤ ↑(m - n : ℕ) :=
  by
  by_cases h : m ≥ n
  · exact le_of_eq (Int.ofNat_sub h).symm
  · simp [le_of_not_ge h, coe_nat_le]
#align int.le_coe_nat_sub Int.le_coe_nat_sub
-/

/-! ### succ and pred -/


#print Int.succ_coe_nat_pos /-
@[simp]
theorem succ_coe_nat_pos (n : ℕ) : 0 < (n : ℤ) + 1 :=
  lt_add_one_iff.mpr (by simp)
#align int.succ_coe_nat_pos Int.succ_coe_nat_pos
-/

/-! ### nat abs -/


variable {a b : ℤ} {n : ℕ}

/- warning: int.nat_abs_eq_iff_sq_eq -> Int.natAbs_eq_iff_sq_eq is a dubious translation:
lean 3 declaration is
  forall {a : Int} {b : Int}, Iff (Eq.{1} Nat (Int.natAbs a) (Int.natAbs b)) (Eq.{1} Int (HPow.hPow.{0, 0, 0} Int Nat Int (instHPow.{0, 0} Int Nat (Monoid.Pow.{0} Int Int.monoid)) a (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) (HPow.hPow.{0, 0, 0} Int Nat Int (instHPow.{0, 0} Int Nat (Monoid.Pow.{0} Int Int.monoid)) b (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))))
but is expected to have type
  forall {a : Int} {b : Int}, Iff (Eq.{1} Nat (Int.natAbs a) (Int.natAbs b)) (Eq.{1} Int (HPow.hPow.{0, 0, 0} Int Nat Int (instHPow.{0, 0} Int Nat (Monoid.Pow.{0} Int Int.instMonoidInt)) a (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) (HPow.hPow.{0, 0, 0} Int Nat Int (instHPow.{0, 0} Int Nat (Monoid.Pow.{0} Int Int.instMonoidInt)) b (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))))
Case conversion may be inaccurate. Consider using '#align int.nat_abs_eq_iff_sq_eq Int.natAbs_eq_iff_sq_eqₓ'. -/
theorem natAbs_eq_iff_sq_eq {a b : ℤ} : a.natAbs = b.natAbs ↔ a ^ 2 = b ^ 2 :=
  by
  rw [sq, sq]
  exact nat_abs_eq_iff_mul_self_eq
#align int.nat_abs_eq_iff_sq_eq Int.natAbs_eq_iff_sq_eq

/- warning: int.nat_abs_lt_iff_sq_lt -> Int.natAbs_lt_iff_sq_lt is a dubious translation:
lean 3 declaration is
  forall {a : Int} {b : Int}, Iff (LT.lt.{0} Nat Nat.hasLt (Int.natAbs a) (Int.natAbs b)) (LT.lt.{0} Int Int.hasLt (HPow.hPow.{0, 0, 0} Int Nat Int (instHPow.{0, 0} Int Nat (Monoid.Pow.{0} Int Int.monoid)) a (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) (HPow.hPow.{0, 0, 0} Int Nat Int (instHPow.{0, 0} Int Nat (Monoid.Pow.{0} Int Int.monoid)) b (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))))
but is expected to have type
  forall {a : Int} {b : Int}, Iff (LT.lt.{0} Nat instLTNat (Int.natAbs a) (Int.natAbs b)) (LT.lt.{0} Int Int.instLTInt (HPow.hPow.{0, 0, 0} Int Nat Int (instHPow.{0, 0} Int Nat (Monoid.Pow.{0} Int Int.instMonoidInt)) a (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) (HPow.hPow.{0, 0, 0} Int Nat Int (instHPow.{0, 0} Int Nat (Monoid.Pow.{0} Int Int.instMonoidInt)) b (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))))
Case conversion may be inaccurate. Consider using '#align int.nat_abs_lt_iff_sq_lt Int.natAbs_lt_iff_sq_ltₓ'. -/
theorem natAbs_lt_iff_sq_lt {a b : ℤ} : a.natAbs < b.natAbs ↔ a ^ 2 < b ^ 2 :=
  by
  rw [sq, sq]
  exact nat_abs_lt_iff_mul_self_lt
#align int.nat_abs_lt_iff_sq_lt Int.natAbs_lt_iff_sq_lt

/- warning: int.nat_abs_le_iff_sq_le -> Int.natAbs_le_iff_sq_le is a dubious translation:
lean 3 declaration is
  forall {a : Int} {b : Int}, Iff (LE.le.{0} Nat Nat.hasLe (Int.natAbs a) (Int.natAbs b)) (LE.le.{0} Int Int.hasLe (HPow.hPow.{0, 0, 0} Int Nat Int (instHPow.{0, 0} Int Nat (Monoid.Pow.{0} Int Int.monoid)) a (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) (HPow.hPow.{0, 0, 0} Int Nat Int (instHPow.{0, 0} Int Nat (Monoid.Pow.{0} Int Int.monoid)) b (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))))
but is expected to have type
  forall {a : Int} {b : Int}, Iff (LE.le.{0} Nat instLENat (Int.natAbs a) (Int.natAbs b)) (LE.le.{0} Int Int.instLEInt (HPow.hPow.{0, 0, 0} Int Nat Int (instHPow.{0, 0} Int Nat (Monoid.Pow.{0} Int Int.instMonoidInt)) a (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) (HPow.hPow.{0, 0, 0} Int Nat Int (instHPow.{0, 0} Int Nat (Monoid.Pow.{0} Int Int.instMonoidInt)) b (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))))
Case conversion may be inaccurate. Consider using '#align int.nat_abs_le_iff_sq_le Int.natAbs_le_iff_sq_leₓ'. -/
theorem natAbs_le_iff_sq_le {a b : ℤ} : a.natAbs ≤ b.natAbs ↔ a ^ 2 ≤ b ^ 2 :=
  by
  rw [sq, sq]
  exact nat_abs_le_iff_mul_self_le
#align int.nat_abs_le_iff_sq_le Int.natAbs_le_iff_sq_le

#print Int.natAbs_inj_of_nonneg_of_nonneg /-
theorem natAbs_inj_of_nonneg_of_nonneg {a b : ℤ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    natAbs a = natAbs b ↔ a = b := by rw [← sq_eq_sq ha hb, ← nat_abs_eq_iff_sq_eq]
#align int.nat_abs_inj_of_nonneg_of_nonneg Int.natAbs_inj_of_nonneg_of_nonneg
-/

#print Int.natAbs_inj_of_nonpos_of_nonpos /-
theorem natAbs_inj_of_nonpos_of_nonpos {a b : ℤ} (ha : a ≤ 0) (hb : b ≤ 0) :
    natAbs a = natAbs b ↔ a = b := by
  simpa only [Int.natAbs_neg, neg_inj] using
    nat_abs_inj_of_nonneg_of_nonneg (neg_nonneg_of_nonpos ha) (neg_nonneg_of_nonpos hb)
#align int.nat_abs_inj_of_nonpos_of_nonpos Int.natAbs_inj_of_nonpos_of_nonpos
-/

#print Int.natAbs_inj_of_nonneg_of_nonpos /-
theorem natAbs_inj_of_nonneg_of_nonpos {a b : ℤ} (ha : 0 ≤ a) (hb : b ≤ 0) :
    natAbs a = natAbs b ↔ a = -b := by
  simpa only [Int.natAbs_neg] using nat_abs_inj_of_nonneg_of_nonneg ha (neg_nonneg_of_nonpos hb)
#align int.nat_abs_inj_of_nonneg_of_nonpos Int.natAbs_inj_of_nonneg_of_nonpos
-/

#print Int.natAbs_inj_of_nonpos_of_nonneg /-
theorem natAbs_inj_of_nonpos_of_nonneg {a b : ℤ} (ha : a ≤ 0) (hb : 0 ≤ b) :
    natAbs a = natAbs b ↔ -a = b := by
  simpa only [Int.natAbs_neg] using nat_abs_inj_of_nonneg_of_nonneg (neg_nonneg_of_nonpos ha) hb
#align int.nat_abs_inj_of_nonpos_of_nonneg Int.natAbs_inj_of_nonpos_of_nonneg
-/

section Intervals

open Set

#print Int.strictMonoOn_natAbs /-
theorem strictMonoOn_natAbs : StrictMonoOn natAbs (Ici 0) := fun a ha b hb hab =>
  natAbs_lt_natAbs_of_nonneg_of_lt ha hab
#align int.strict_mono_on_nat_abs Int.strictMonoOn_natAbs
-/

#print Int.strictAntiOn_natAbs /-
theorem strictAntiOn_natAbs : StrictAntiOn natAbs (Iic 0) := fun a ha b hb hab => by
  simpa [Int.natAbs_neg] using
    nat_abs_lt_nat_abs_of_nonneg_of_lt (right.nonneg_neg_iff.mpr hb) (neg_lt_neg_iff.mpr hab)
#align int.strict_anti_on_nat_abs Int.strictAntiOn_natAbs
-/

#print Int.injOn_natAbs_Ici /-
theorem injOn_natAbs_Ici : InjOn natAbs (Ici 0) :=
  strictMonoOn_natAbs.InjOn
#align int.inj_on_nat_abs_Ici Int.injOn_natAbs_Ici
-/

#print Int.injOn_natAbs_Iic /-
theorem injOn_natAbs_Iic : InjOn natAbs (Iic 0) :=
  strictAntiOn_natAbs.InjOn
#align int.inj_on_nat_abs_Iic Int.injOn_natAbs_Iic
-/

end Intervals

/-! ### to_nat -/


#print Int.toNat_of_nonpos /-
theorem toNat_of_nonpos : ∀ {z : ℤ}, z ≤ 0 → z.toNat = 0
  | 0, _ => rfl
  | (n + 1 : ℕ), h => (h.not_lt (by simp)).elim
  | -[n+1], _ => rfl
#align int.to_nat_of_nonpos Int.toNat_of_nonpos
-/

/-! ### bitwise ops

This lemma is orphaned from `data.int.bitwise` as it also requires material from `data.int.order`.
-/


attribute [local simp] Int.zero_div

#print Int.div2_bit /-
@[simp]
theorem div2_bit (b n) : div2 (bit b n) = n :=
  by
  rw [bit_val, div2_val, add_comm, Int.add_mul_ediv_left, (_ : (_ / 2 : ℤ) = 0), zero_add]
  cases b
  · simp
  · show of_nat _ = _
    rw [Nat.div_eq_zero] <;> simp
  · cc
#align int.div2_bit Int.div2_bit
-/

end Int

