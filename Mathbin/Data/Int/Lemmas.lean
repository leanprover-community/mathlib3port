/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad
-/
import Mathbin.Data.Int.Order
import Mathbin.Data.Int.Bitwise
import Mathbin.Data.Nat.Cast.Basic

/-!
# Miscellaneous lemmas about the integers

This file contains lemmas about integers, which require further imports than
`data.int.basic` or `data.int.order`.

-/


open Nat

namespace Int

theorem le_coe_nat_sub (m n : ℕ) : (m - n : ℤ) ≤ ↑(m - n : ℕ) := by
  by_cases h:m ≥ n
  · exact le_of_eq (Int.coe_nat_sub h).symm
    
  · simp [le_of_not_ge h, coe_nat_le]
    

/-! ### succ and pred -/


@[simp]
theorem succ_coe_nat_pos (n : ℕ) : 0 < (n : ℤ) + 1 :=
  lt_add_one_iff.mpr (by simp)

/-! ### nat abs -/


variable {a b : ℤ} {n : ℕ}

theorem nat_abs_eq_iff_sq_eq {a b : ℤ} : a.natAbs = b.natAbs ↔ a ^ 2 = b ^ 2 := by
  rw [sq, sq]
  exact nat_abs_eq_iff_mul_self_eq

theorem nat_abs_lt_iff_sq_lt {a b : ℤ} : a.natAbs < b.natAbs ↔ a ^ 2 < b ^ 2 := by
  rw [sq, sq]
  exact nat_abs_lt_iff_mul_self_lt

theorem nat_abs_le_iff_sq_le {a b : ℤ} : a.natAbs ≤ b.natAbs ↔ a ^ 2 ≤ b ^ 2 := by
  rw [sq, sq]
  exact nat_abs_le_iff_mul_self_le

theorem nat_abs_inj_of_nonneg_of_nonneg {a b : ℤ} (ha : 0 ≤ a) (hb : 0 ≤ b) : natAbs a = natAbs b ↔ a = b := by
  rw [← sq_eq_sq ha hb, ← nat_abs_eq_iff_sq_eq]

theorem nat_abs_inj_of_nonpos_of_nonpos {a b : ℤ} (ha : a ≤ 0) (hb : b ≤ 0) : natAbs a = natAbs b ↔ a = b := by
  simpa only [Int.nat_abs_neg, neg_inj] using
    nat_abs_inj_of_nonneg_of_nonneg (neg_nonneg_of_nonpos ha) (neg_nonneg_of_nonpos hb)

theorem nat_abs_inj_of_nonneg_of_nonpos {a b : ℤ} (ha : 0 ≤ a) (hb : b ≤ 0) : natAbs a = natAbs b ↔ a = -b := by
  simpa only [Int.nat_abs_neg] using nat_abs_inj_of_nonneg_of_nonneg ha (neg_nonneg_of_nonpos hb)

theorem nat_abs_inj_of_nonpos_of_nonneg {a b : ℤ} (ha : a ≤ 0) (hb : 0 ≤ b) : natAbs a = natAbs b ↔ -a = b := by
  simpa only [Int.nat_abs_neg] using nat_abs_inj_of_nonneg_of_nonneg (neg_nonneg_of_nonpos ha) hb

section Intervals

open Set

theorem strict_mono_on_nat_abs : StrictMonoOn natAbs (IciCat 0) := fun a ha b hb hab =>
  nat_abs_lt_nat_abs_of_nonneg_of_lt ha hab

theorem strict_anti_on_nat_abs : StrictAntiOn natAbs (IicCat 0) := fun a ha b hb hab => by
  simpa [Int.nat_abs_neg] using
    nat_abs_lt_nat_abs_of_nonneg_of_lt (right.nonneg_neg_iff.mpr hb) (neg_lt_neg_iff.mpr hab)

theorem inj_on_nat_abs_Ici : InjOn natAbs (IciCat 0) :=
  strict_mono_on_nat_abs.InjOn

theorem inj_on_nat_abs_Iic : InjOn natAbs (IicCat 0) :=
  strict_anti_on_nat_abs.InjOn

end Intervals

/-! ### to_nat -/


theorem to_nat_of_nonpos : ∀ {z : ℤ}, z ≤ 0 → z.toNat = 0
  | 0, _ => rfl
  | (n + 1 : ℕ), h => (h.not_lt (by simp)).elim
  | -[n+1], _ => rfl

/-! ### bitwise ops

This lemma is orphaned from `data.int.bitwise` as it also requires material from `data.int.order`.
-/


attribute [local simp] Int.zero_div

@[simp]
theorem div2_bit (b n) : div2 (bit b n) = n := by
  rw [bit_val, div2_val, add_comm, Int.add_mul_div_left, (_ : (_ / 2 : ℤ) = 0), zero_add]
  cases b
  · simp
    
  · show of_nat _ = _
    rw [Nat.div_eq_zero] <;> simp
    
  · cc
    

end Int

