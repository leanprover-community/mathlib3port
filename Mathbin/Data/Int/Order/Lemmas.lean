/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad

! This file was ported from Lean 3 source module data.int.order.lemmas
! leanprover-community/mathlib commit c3291da49cfa65f0d43b094750541c0731edc932
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Int.Order.Basic
import Mathbin.Algebra.GroupWithZero.Divisibility
import Mathbin.Algebra.Order.Ring.Abs

/-!
# Further lemmas about the integers

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.
The distinction between this file and `data.int.order.basic` is not particularly clear.
They are separated by now to minimize the porting requirements for tactics during the transition to
mathlib4. After `data.rat.order` has been ported, please feel free to reorganize these two files.
-/


open Nat

namespace Int

/-! ### nat abs -/


variable {a b : ℤ} {n : ℕ}

#print Int.natAbs_eq_iff_mul_self_eq /-
theorem natAbs_eq_iff_mul_self_eq {a b : ℤ} : a.natAbs = b.natAbs ↔ a * a = b * b :=
  by
  rw [← abs_eq_iff_mul_self_eq, abs_eq_nat_abs, abs_eq_nat_abs]
  exact int.coe_nat_inj'.symm
#align int.nat_abs_eq_iff_mul_self_eq Int.natAbs_eq_iff_mul_self_eq
-/

#print Int.eq_natAbs_iff_mul_eq_zero /-
theorem eq_natAbs_iff_mul_eq_zero : a.natAbs = n ↔ (a - n) * (a + n) = 0 := by
  rw [nat_abs_eq_iff, mul_eq_zero, sub_eq_zero, add_eq_zero_iff_eq_neg]
#align int.eq_nat_abs_iff_mul_eq_zero Int.eq_natAbs_iff_mul_eq_zero
-/

#print Int.natAbs_lt_iff_mul_self_lt /-
theorem natAbs_lt_iff_mul_self_lt {a b : ℤ} : a.natAbs < b.natAbs ↔ a * a < b * b :=
  by
  rw [← abs_lt_iff_mul_self_lt, abs_eq_nat_abs, abs_eq_nat_abs]
  exact int.coe_nat_lt.symm
#align int.nat_abs_lt_iff_mul_self_lt Int.natAbs_lt_iff_mul_self_lt
-/

#print Int.natAbs_le_iff_mul_self_le /-
theorem natAbs_le_iff_mul_self_le {a b : ℤ} : a.natAbs ≤ b.natAbs ↔ a * a ≤ b * b :=
  by
  rw [← abs_le_iff_mul_self_le, abs_eq_nat_abs, abs_eq_nat_abs]
  exact int.coe_nat_le.symm
#align int.nat_abs_le_iff_mul_self_le Int.natAbs_le_iff_mul_self_le
-/

#print Int.dvd_div_of_mul_dvd /-
theorem dvd_div_of_mul_dvd {a b c : ℤ} (h : a * b ∣ c) : b ∣ c / a :=
  by
  rcases eq_or_ne a 0 with (rfl | ha)
  · simp only [Int.div_zero, dvd_zero]
  rcases h with ⟨d, rfl⟩
  refine' ⟨d, _⟩
  rw [mul_assoc, Int.mul_ediv_cancel_left _ ha]
#align int.dvd_div_of_mul_dvd Int.dvd_div_of_mul_dvd
-/

/-! ### units -/


#print Int.eq_zero_of_abs_lt_dvd /-
theorem eq_zero_of_abs_lt_dvd {m x : ℤ} (h1 : m ∣ x) (h2 : |x| < m) : x = 0 :=
  by
  by_cases hm : m = 0; · subst m; exact zero_dvd_iff.mp h1
  rcases h1 with ⟨d, rfl⟩
  apply mul_eq_zero_of_right
  rw [← abs_lt_one_iff, ← mul_lt_iff_lt_one_right (abs_pos.mpr hm), ← abs_mul]
  exact lt_of_lt_of_le h2 (le_abs_self m)
#align int.eq_zero_of_abs_lt_dvd Int.eq_zero_of_abs_lt_dvd
-/

end Int

