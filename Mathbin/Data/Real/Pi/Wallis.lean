/-
Copyright (c) 2021 Hanting Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hanting Zhang

! This file was ported from Lean 3 source module data.real.pi.wallis
! leanprover-community/mathlib commit bcfa726826abd57587355b4b5b7e78ad6527b7e4
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Analysis.SpecialFunctions.Integrals

/-! # The Wallis formula for Pi

This file establishes the Wallis product for `π` (`real.tendsto_prod_pi_div_two`). Our proof is
largely about analyzing the behaviour of the sequence `∫ x in 0..π, sin x ^ n` as `n → ∞`.
See: https://en.wikipedia.org/wiki/Wallis_product

The proof can be broken down into two pieces. The first step (carried out in
`analysis.special_functions.integrals`) is to use repeated integration by parts to obtain an
explicit formula for this integral, which is rational if `n` is odd and a rational multiple of `π`
if `n` is even.

The second step, carried out here, is to estimate the ratio
`∫ (x : ℝ) in 0..π, sin x ^ (2 * k + 1) / ∫ (x : ℝ) in 0..π, sin x ^ (2 * k)` and prove that
it converges to one using the squeeze theorem. The final product for `π` is obtained after some
algebraic manipulation.

## Main statements

* `real.wallis.W`: the product of the first `k` terms in Wallis' formula for `π`.
* `real.wallis.W_eq_integral_sin_pow_div_integral_sin_pow`: express `W n` as a ratio of integrals.
* `real.wallis.W_le` and `real.wallis.le_W`: upper and lower bounds for `W n`.
* `real.wallis.integral_sin_pow_odd_sq_eq` and `real.wallis.integral_sin_pow_even_sq_eq`: formulas
  for `(∫ x in 0..π, sin x ^ n) ^ 2` in terms of `W`.
* `integral_sin_pow_le` and `le_integral_sin_pow`: bounds for `∫ x in 0..π, sin x ^ n`.
* `real.tendsto_prod_pi_div_two`: the Wallis product formula.
 -/


open Real Topology BigOperators Nat

open Filter Finset intervalIntegral

namespace Real

namespace Wallis

/-- The product of the first `k` terms in Wallis' formula for `π`. -/
noncomputable def w (k : ℕ) : ℝ :=
  ∏ i in range k, (2 * i + 2) / (2 * i + 1) * ((2 * i + 2) / (2 * i + 3))
#align real.wallis.W Real.Wallis.w

theorem w_succ (k : ℕ) :
    w (k + 1) = w k * ((2 * k + 2) / (2 * k + 1) * ((2 * k + 2) / (2 * k + 3))) :=
  prod_range_succ _ _
#align real.wallis.W_succ Real.Wallis.w_succ

theorem w_pos (k : ℕ) : 0 < w k := by
  induction' k with k hk
  · unfold W
    simp
  · rw [W_succ]
    refine' mul_pos hk (mul_pos (div_pos _ _) (div_pos _ _)) <;> positivity
#align real.wallis.W_pos Real.Wallis.w_pos

theorem w_eq_factorial_ratio (n : ℕ) : w n = 2 ^ (4 * n) * n ! ^ 4 / ((2 * n)! ^ 2 * (2 * n + 1)) :=
  by
  induction' n with n IH
  ·
    simp only [W, prod_range_zero, Nat.factorial_zero, mul_zero, pow_zero, algebraMap.coe_one,
      one_pow, mul_one, algebraMap.coe_zero, zero_add, div_self, Ne.def, one_ne_zero, not_false_iff]
  · unfold W at IH⊢
    rw [prod_range_succ, IH, _root_.div_mul_div_comm, _root_.div_mul_div_comm]
    refine' (div_eq_div_iff _ _).mpr _
    any_goals exact ne_of_gt (by positivity)
    simp_rw [Nat.mul_succ, Nat.factorial_succ, pow_succ]
    push_cast
    ring_nf
#align real.wallis.W_eq_factorial_ratio Real.Wallis.w_eq_factorial_ratio

theorem w_eq_integral_sin_pow_div_integral_sin_pow (k : ℕ) :
    (π / 2)⁻¹ * w k = (∫ x : ℝ in 0 ..π, sin x ^ (2 * k + 1)) / ∫ x : ℝ in 0 ..π, sin x ^ (2 * k) :=
  by
  rw [integral_sin_pow_even, integral_sin_pow_odd, mul_div_mul_comm, ← prod_div_distrib, inv_div]
  simp_rw [div_div_div_comm, div_div_eq_mul_div, mul_div_assoc]
  rfl
#align real.wallis.W_eq_integral_sin_pow_div_integral_sin_pow Real.Wallis.w_eq_integral_sin_pow_div_integral_sin_pow

theorem w_le (k : ℕ) : w k ≤ π / 2 :=
  by
  rw [← div_le_one pi_div_two_pos, div_eq_inv_mul]
  rw [W_eq_integral_sin_pow_div_integral_sin_pow, div_le_one (integral_sin_pow_pos _)]
  apply integral_sin_pow_succ_le
#align real.wallis.W_le Real.Wallis.w_le

theorem le_w (k : ℕ) : ((2 : ℝ) * k + 1) / (2 * k + 2) * (π / 2) ≤ w k :=
  by
  rw [← le_div_iff pi_div_two_pos, div_eq_inv_mul (W k) _]
  rw [W_eq_integral_sin_pow_div_integral_sin_pow, le_div_iff (integral_sin_pow_pos _)]
  convert integral_sin_pow_succ_le (2 * k + 1)
  rw [integral_sin_pow (2 * k)]
  simp only [sin_zero, zero_pow', Ne.def, Nat.succ_ne_zero, not_false_iff, zero_mul, sin_pi,
    tsub_zero, Nat.cast_mul, Nat.cast_bit0, algebraMap.coe_one, zero_div, zero_add]
#align real.wallis.le_W Real.Wallis.le_w

theorem tendsto_w_nhds_pi_div_two : Tendsto w atTop (𝓝 <| π / 2) :=
  by
  refine' tendsto_of_tendsto_of_tendsto_of_le_of_le _ tendsto_const_nhds le_W W_le
  have : 𝓝 (π / 2) = 𝓝 ((1 - 0) * (π / 2)) := by rw [sub_zero, one_mul]
  rw [this]
  refine' tendsto.mul _ tendsto_const_nhds
  have h : ∀ n : ℕ, ((2 : ℝ) * n + 1) / (2 * n + 2) = 1 - 1 / (2 * n + 2) :=
    by
    intro n
    rw [sub_div' _ _ _
        (ne_of_gt
          (add_pos_of_nonneg_of_pos (mul_nonneg (two_pos : 0 < (2 : ℝ)).le (Nat.cast_nonneg _))
            two_pos)),
      one_mul]
    congr 1
    ring
  simp_rw [h]
  refine' (tendsto_const_nhds.div_at_top _).const_sub _
  refine' tendsto.at_top_add _ tendsto_const_nhds
  exact tendsto_coe_nat_at_top_at_top.const_mul_at_top two_pos
#align real.wallis.tendsto_W_nhds_pi_div_two Real.Wallis.tendsto_w_nhds_pi_div_two

theorem w_eq_mul_sq (k : ℕ) :
    w k = (2 * k + 1) * (∏ i in range k, ((2 : ℝ) * i + 2) / (2 * i + 3)) ^ 2 :=
  by
  induction' k with k hk
  · simp [W]
  · unfold W at *
    rw [prod_range_succ, prod_range_succ, hk]
    suffices
      ∀ x : ℝ,
        (2 * ↑k + 1) * x ^ 2 * ((2 * ↑k + 2) / (2 * ↑k + 1) * ((2 * ↑k + 2) / (2 * ↑k + 3))) =
          (2 * ↑k.succ + 1) * (x * ((2 * ↑k + 2) / (2 * ↑k + 3))) ^ 2
      by rw [this]
    intro x
    have a : (2 * ↑k + 1 : ℝ) ≠ 0 := by positivity
    have b : (2 * ↑k + 3 : ℝ) ≠ 0 := by positivity
    field_simp
    ring
#align real.wallis.W_eq_mul_sq Real.Wallis.w_eq_mul_sq

theorem integral_sin_pow_odd_sq_eq (k : ℕ) :
    (∫ x in 0 ..π, sin x ^ (2 * k + 1)) ^ 2 = 4 * w k / (2 * k + 1) :=
  by
  rw [integral_sin_pow_odd]
  have B := W_eq_mul_sq k
  rw [mul_comm (2 * (k : ℝ) + 1) _, ← div_eq_iff] at B
  · rw [mul_pow, ← B]
    ring
  · positivity
#align real.wallis.integral_sin_pow_odd_sq_eq Real.Wallis.integral_sin_pow_odd_sq_eq

theorem integral_sin_pow_even_sq_eq (k : ℕ) :
    (∫ x in 0 ..π, sin x ^ (2 * k)) ^ 2 = π ^ 2 / (2 * k + 1) / w k :=
  by
  induction' k with k hk
  · dsimp only [W]
    simp
  · have np : 0 < 2 * (k : ℝ) + 1 := by positivity
    rw [Nat.succ_eq_add_one, mul_add 2 k 1, mul_one, integral_sin_pow, sin_zero, sin_pi,
      zero_pow (Nat.add_pos_right _ zero_lt_one), zero_mul, zero_mul, sub_zero, zero_div, zero_add,
      mul_pow, hk, W_succ, Nat.cast_add_one, Nat.cast_mul, mul_add, mul_one,
      add_assoc (2 * (k : ℝ)) 2 1, (by ring : (2 : ℝ) + 1 = 3), sq]
    have np2 : 2 * (k : ℝ) + 2 ≠ 0 := by positivity
    have np3 : 2 * (k : ℝ) + 3 ≠ 0 := by positivity
    field_simp [np.ne', (W_pos k).ne']
    ring
#align real.wallis.integral_sin_pow_even_sq_eq Real.Wallis.integral_sin_pow_even_sq_eq

end Wallis

end Real

open Real Real.Wallis

section IntegralSinPowBounds

/-! ## Bounds for integrals of `sin x ^ n`

Explicit `O(1/√n)` bounds for `∫ x in 0..π, sin x ^ n`, as a by-product of the proof of Wallis'
formula for `π`. -/


theorem integral_sin_pow_odd_le (n : ℕ) :
    (∫ x in 0 ..π, sin x ^ (2 * n + 1)) ≤ sqrt (2 * π / (2 * n + 1)) :=
  by
  have np : 0 < 2 * (n : ℝ) + 1 := by positivity
  rw [le_sqrt (integral_sin_pow_pos _).le (div_pos two_pi_pos np).le, integral_sin_pow_odd_sq_eq]
  apply div_le_div_of_le np.le
  rw [← le_div_iff' (by norm_num : 0 < (4 : ℝ))]
  convert W_le n using 1
  ring
#align integral_sin_pow_odd_le integral_sin_pow_odd_le

theorem integral_sin_pow_even_le (n : ℕ) :
    (∫ x in 0 ..π, sin x ^ (2 * n)) ≤ sqrt (2 * π * (2 * n + 2) / (2 * n + 1) ^ 2) :=
  by
  have np : 0 < 2 * (n : ℝ) + 1 := by positivity
  have np' : 0 < 2 * (n : ℝ) + 2 := by positivity
  rw [le_sqrt (integral_sin_pow_pos _).le]
  swap
  · refine' div_nonneg _ (sq_nonneg _)
    exact mul_nonneg two_pi_pos.le np'.le
  rw [integral_sin_pow_even_sq_eq, div_le_iff (W_pos n), ← div_le_iff']
  swap
  · refine' div_pos _ (sq_pos_of_pos np)
    exact mul_pos two_pi_pos np'
  convert le_W n
  field_simp [np.ne', np'.ne', pi_pos.ne']
  ring
#align integral_sin_pow_even_le integral_sin_pow_even_le

theorem integral_sin_pow_le {n : ℕ} (hn : n ≠ 0) : (∫ x in 0 ..π, sin x ^ n) ≤ sqrt (2 * π / n) :=
  by
  -- this is a slightly weaker bound than `integral_sin_pow_even_le` for even `n`, but uniform in
  -- its statement
  obtain ⟨k, hk⟩ := Nat.even_or_odd' n
  rcases hk with (rfl | rfl)
  · refine' le_trans (integral_sin_pow_even_le k) _
    apply sqrt_le_sqrt
    rw [div_le_div_iff, mul_assoc, mul_le_mul_left two_pi_pos]
    rotate_left
    · positivity
    · positivity
    have : (2 * (k : ℝ) + 2) * ((2 * k : ℕ) : ℝ) = (2 * k + 1) ^ 2 - 1 :=
      by
      push_cast
      ring
    rw [this, sub_le_self_iff]
    exact zero_le_one
  · convert integral_sin_pow_odd_le k using 3
    rw [Nat.cast_add, Nat.cast_mul, Nat.cast_two, Nat.cast_one]
#align integral_sin_pow_le integral_sin_pow_le

theorem le_integral_sin_pow (n : ℕ) : sqrt (2 * π / (n + 1)) ≤ ∫ x in 0 ..π, sin x ^ n :=
  by
  refine' sqrt_le_iff.mpr ⟨(integral_sin_pow_pos _).le, _⟩
  obtain ⟨k, hk⟩ := Nat.even_or_odd' n
  have np : 0 < 2 * (k : ℝ) + 1 := by positivity
  have np' : 2 * (k : ℝ) + 2 ≠ 0 := by positivity
  rcases hk with (rfl | rfl)
  · rw [integral_sin_pow_even_sq_eq, le_div_iff (W_pos _), Nat.cast_mul, Nat.cast_two, ←
      le_div_iff' (div_pos two_pi_pos np)]
    convert W_le k using 1
    field_simp [np.ne', np', pi_pos.ne']
    ring
  · rw [Nat.cast_add, Nat.cast_mul, Nat.cast_two, Nat.cast_one,
      (by ring : (2 : ℝ) * k + 1 + 1 = 2 * k + 2), integral_sin_pow_odd_sq_eq, le_div_iff np, ←
      div_le_iff' (by positivity : 0 < (4 : ℝ))]
    convert le_W k
    field_simp [np.ne', np']
    ring
#align le_integral_sin_pow le_integral_sin_pow

end IntegralSinPowBounds

/-- Wallis' product formula for `π / 2`. -/
theorem Real.tendsto_prod_pi_div_two :
    Tendsto (fun k => ∏ i in range k, ((2 : ℝ) * i + 2) / (2 * i + 1) * ((2 * i + 2) / (2 * i + 3)))
      atTop (𝓝 (π / 2)) :=
  tendsto_w_nhds_pi_div_two
#align real.tendsto_prod_pi_div_two Real.tendsto_prod_pi_div_two

