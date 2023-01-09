/-
Copyright (c) 2022 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler

! This file was ported from Lean 3 source module analysis.special_functions.trigonometric.bounds
! leanprover-community/mathlib commit 40acfb6aa7516ffe6f91136691df012a64683390
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathbin.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv

/-!
# Polynomial bounds for trigonometric functions

## Main statements

This file contains upper and lower bounds for real trigonometric functions in terms
of polynomials. See `trigonometric.basic` for more elementary inequalities, establishing
the ranges of these functions, and their monotonicity in suitable intervals.

Here we prove the following:

* `sin_lt`: for `x > 0` we have `sin x < x`.
* `sin_gt_sub_cube`: For `0 < x ≤ 1` we have `x - x ^ 3 / 4 < sin x`.
* `lt_tan`: for `0 < x < π/2` we have `x < tan x`.

## Tags

sin, cos, tan, angle
-/


noncomputable section

open Set

namespace Real

open Real

/-- For 0 < x, we have sin x < x. -/
theorem sin_lt {x : ℝ} (h : 0 < x) : sin x < x :=
  by
  cases' lt_or_le 1 x with h' h'
  · exact (sin_le_one x).trans_lt h'
  have hx : |x| = x := abs_of_nonneg h.le
  have := le_of_abs_le (sin_bound <| show |x| ≤ 1 by rwa [hx])
  rw [sub_le_iff_le_add', hx] at this
  apply this.trans_lt
  rw [sub_add, sub_lt_self_iff, sub_pos, div_eq_mul_inv (x ^ 3)]
  refine' mul_lt_mul' _ (by norm_num) (by norm_num) (pow_pos h 3)
  apply pow_le_pow_of_le_one h.le h'
  norm_num
#align real.sin_lt Real.sin_lt

/-- For 0 < x ≤ 1 we have x - x ^ 3 / 4 < sin x.

This is also true for x > 1, but it's nontrivial for x just above 1. This inequality is not
tight; the tighter inequality is sin x > x - x ^ 3 / 6 for all x > 0, but this inequality has
a simpler proof. -/
theorem sin_gt_sub_cube {x : ℝ} (h : 0 < x) (h' : x ≤ 1) : x - x ^ 3 / 4 < sin x :=
  by
  have hx : |x| = x := abs_of_nonneg h.le
  have := neg_le_of_abs_le (sin_bound <| show |x| ≤ 1 by rwa [hx])
  rw [le_sub_iff_add_le, hx] at this
  refine' lt_of_lt_of_le _ this
  have : x ^ 3 / 4 - x ^ 3 / 6 = x ^ 3 * 12⁻¹ := by norm_num [div_eq_mul_inv, ← mul_sub]
  rw [add_comm, sub_add, sub_neg_eq_add, sub_lt_sub_iff_left, ← lt_sub_iff_add_lt', this]
  refine' mul_lt_mul' _ (by norm_num) (by norm_num) (pow_pos h 3)
  apply pow_le_pow_of_le_one h.le h'
  norm_num
#align real.sin_gt_sub_cube Real.sin_gt_sub_cube

/-- The derivative of `tan x - x` is `1/(cos x)^2 - 1` away from the zeroes of cos. -/
theorem deriv_tan_sub_id (x : ℝ) (h : cos x ≠ 0) :
    deriv (fun y : ℝ => tan y - y) x = 1 / cos x ^ 2 - 1 :=
  HasDerivAt.deriv <| by simpa using (has_deriv_at_tan h).add (has_deriv_at_id x).neg
#align real.deriv_tan_sub_id Real.deriv_tan_sub_id

/-- For all `0 ≤ x < π/2` we have `x < tan x`.

This is proved by checking that the function `tan x - x` vanishes
at zero and has non-negative derivative. -/
theorem lt_tan (x : ℝ) (h1 : 0 < x) (h2 : x < π / 2) : x < tan x :=
  by
  let U := Ico 0 (π / 2)
  have intU : interior U = Ioo 0 (π / 2) := interior_Ico
  have half_pi_pos : 0 < π / 2 := div_pos pi_pos two_pos
  have cos_pos : ∀ {y : ℝ}, y ∈ U → 0 < cos y :=
    by
    intro y hy
    exact cos_pos_of_mem_Ioo (Ico_subset_Ioo_left (neg_lt_zero.mpr half_pi_pos) hy)
  have sin_pos : ∀ {y : ℝ}, y ∈ interior U → 0 < sin y :=
    by
    intro y hy
    rw [intU] at hy
    exact sin_pos_of_mem_Ioo (Ioo_subset_Ioo_right (div_le_self pi_pos.le one_le_two) hy)
  have tan_cts_U : ContinuousOn tan U :=
    by
    apply ContinuousOn.mono continuous_on_tan
    intro z hz
    simp only [mem_set_of_eq]
    exact (cos_pos hz).ne'
  have tan_minus_id_cts : ContinuousOn (fun y : ℝ => tan y - y) U := tan_cts_U.sub continuous_on_id
  have deriv_pos : ∀ y : ℝ, y ∈ interior U → 0 < deriv (fun y' : ℝ => tan y' - y') y :=
    by
    intro y hy
    have := cos_pos (interior_subset hy)
    simp only [deriv_tan_sub_id y this.ne', one_div, gt_iff_lt, sub_pos]
    have bd2 : cos y ^ 2 < 1 := by
      apply lt_of_le_of_ne y.cos_sq_le_one
      rw [cos_sq']
      simpa only [Ne.def, sub_eq_self, pow_eq_zero_iff, Nat.succ_pos'] using (sin_pos hy).ne'
    rwa [lt_inv, inv_one]
    · exact zero_lt_one
    simpa only [sq, mul_self_pos] using this.ne'
  have mono := Convex.strict_mono_on_of_deriv_pos (convex_Ico 0 (π / 2)) tan_minus_id_cts deriv_pos
  have zero_in_U : (0 : ℝ) ∈ U := by rwa [left_mem_Ico]
  have x_in_U : x ∈ U := ⟨h1.le, h2⟩
  simpa only [tan_zero, sub_zero, sub_pos] using mono zero_in_U x_in_U h1
#align real.lt_tan Real.lt_tan

end Real

