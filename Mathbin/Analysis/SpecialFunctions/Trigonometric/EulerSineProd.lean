/-
Copyright (c) 2023 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler

! This file was ported from Lean 3 source module analysis.special_functions.trigonometric.euler_sine_prod
! leanprover-community/mathlib commit bcfa726826abd57587355b4b5b7e78ad6527b7e4
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Analysis.SpecialFunctions.Integrals
import Mathbin.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathbin.Data.Real.Pi.Wallis

/-! # Euler's infinite product for the sine function

This file proves the infinite product formula

$$ \sin \pi z = \pi z \prod_{n = 1}^\infty \left(1 - \frac{z ^ 2}{n ^ 2}\right) $$

for any real or complex `z`. Our proof closely follows the article
[Salwinski, *Euler's Sine Product Formula: An Elementary Proof*][salwinski2018]: the basic strategy
is to prove a recurrence relation for the integrals `∫ x in 0..π/2, cos 2 z x * cos x ^ (2 * n)`,
generalising the arguments used to prove Wallis' limit formula for `π`.
-/


open Real Topology BigOperators

open Real Set Filter intervalIntegral MeasureTheory.MeasureSpace

namespace EulerSine

section IntegralRecursion

/-! ## Recursion formula for the integral of `cos (2 * z * x) * cos x ^ n`

We evaluate the integral of `cos (2 * z * x) * cos x ^ n`, for any complex `z` and even integers
`n`, via repeated integration by parts. -/


variable {z : ℂ} {n : ℕ}

theorem antideriv_cos_comp_const_mul (hz : z ≠ 0) (x : ℝ) :
    HasDerivAt (fun y : ℝ => Complex.sin (2 * z * y) / (2 * z)) (Complex.cos (2 * z * x)) x :=
  by
  have a : HasDerivAt _ _ ↑x := hasDerivAt_mul_const _
  have b : HasDerivAt (fun y : ℂ => Complex.sin (y * (2 * z))) _ ↑x :=
    HasDerivAt.comp x (Complex.hasDerivAt_sin (x * (2 * z))) a
  convert b.comp_of_real.div_const (2 * z)
  · ext1 x
    rw [mul_comm _ (2 * z)]
  · field_simp
    rw [mul_comm _ (2 * z)]
#align euler_sine.antideriv_cos_comp_const_mul EulerSine.antideriv_cos_comp_const_mul

theorem antideriv_sin_comp_const_mul (hz : z ≠ 0) (x : ℝ) :
    HasDerivAt (fun y : ℝ => -Complex.cos (2 * z * y) / (2 * z)) (Complex.sin (2 * z * x)) x :=
  by
  have a : HasDerivAt _ _ ↑x := hasDerivAt_mul_const _
  have b : HasDerivAt (fun y : ℂ => Complex.cos (y * (2 * z))) _ ↑x :=
    HasDerivAt.comp x (Complex.hasDerivAt_cos (x * (2 * z))) a
  convert (b.comp_of_real.div_const (2 * z)).neg
  · ext1 x
    rw [mul_comm _ (2 * z)]
    field_simp
  · field_simp
    rw [mul_comm _ (2 * z)]
#align euler_sine.antideriv_sin_comp_const_mul EulerSine.antideriv_sin_comp_const_mul

theorem integral_cos_mul_cos_pow_aux (hn : 2 ≤ n) (hz : z ≠ 0) :
    (∫ x : ℝ in 0 ..π / 2, Complex.cos (2 * z * x) * cos x ^ n) =
      n / (2 * z) * ∫ x : ℝ in 0 ..π / 2, Complex.sin (2 * z * x) * sin x * cos x ^ (n - 1) :=
  by
  have der1 :
    ∀ x : ℝ,
      x ∈ uIcc 0 (π / 2) →
        HasDerivAt (fun y => ↑(cos y) ^ n : ℝ → ℂ) (-n * sin x * cos x ^ (n - 1)) x :=
    by
    intro x hx
    have b : HasDerivAt (fun y => ↑(cos y) : ℝ → ℂ) (-sin x) x := by
      simpa using (has_deriv_at_cos x).of_real_comp
    convert HasDerivAt.comp x (hasDerivAt_pow _ _) b using 1
    ring
  convert integral_mul_deriv_eq_deriv_mul der1 (fun x hx => antideriv_cos_comp_const_mul hz x) _ _
  · ext1 x
    rw [mul_comm]
  · rw [Complex.of_real_zero, mul_zero, Complex.sin_zero, zero_div, mul_zero, sub_zero,
      cos_pi_div_two, Complex.of_real_zero, zero_pow (by positivity : 0 < n), zero_mul, zero_sub, ←
      integral_neg, ← integral_const_mul]
    refine' integral_congr fun x hx => _
    field_simp
    ring
  · apply Continuous.intervalIntegrable
    exact
      (continuous_const.mul (complex.continuous_of_real.comp continuous_sin)).mul
        ((complex.continuous_of_real.comp continuous_cos).pow (n - 1))
  · apply Continuous.intervalIntegrable
    exact complex.continuous_cos.comp (continuous_const.mul Complex.continuous_of_real)
#align euler_sine.integral_cos_mul_cos_pow_aux EulerSine.integral_cos_mul_cos_pow_aux

theorem integral_sin_mul_sin_mul_cos_pow_eq (hn : 2 ≤ n) (hz : z ≠ 0) :
    (∫ x : ℝ in 0 ..π / 2, Complex.sin (2 * z * x) * sin x * cos x ^ (n - 1)) =
      (n / (2 * z) * ∫ x : ℝ in 0 ..π / 2, Complex.cos (2 * z * x) * cos x ^ n) -
        (n - 1) / (2 * z) * ∫ x : ℝ in 0 ..π / 2, Complex.cos (2 * z * x) * cos x ^ (n - 2) :=
  by
  have der1 :
    ∀ x : ℝ,
      x ∈ uIcc 0 (π / 2) →
        HasDerivAt (fun y => sin y * cos y ^ (n - 1) : ℝ → ℂ)
          (cos x ^ n - (n - 1) * sin x ^ 2 * cos x ^ (n - 2)) x :=
    by
    intro x hx
    have c := HasDerivAt.comp (x : ℂ) (hasDerivAt_pow (n - 1) _) (Complex.hasDerivAt_cos x)
    convert ((Complex.hasDerivAt_sin x).mul c).comp_of_real using 1
    · ext1 y
      simp only [Complex.of_real_sin, Complex.of_real_cos]
    · simp only [Complex.of_real_cos, Complex.of_real_sin]
      rw [mul_neg, mul_neg, ← sub_eq_add_neg, Function.comp_apply]
      congr 1
      · rw [← pow_succ, Nat.sub_add_cancel (by linarith : 1 ≤ n)]
      · have : ((n - 1 : ℕ) : ℂ) = (n : ℂ) - 1 := by
          rw [Nat.cast_sub (one_le_two.trans hn), Nat.cast_one]
        rw [Nat.sub_sub, this]
        ring
  convert
    integral_mul_deriv_eq_deriv_mul der1 (fun x hx => antideriv_sin_comp_const_mul hz x) _ _ using 1
  · refine' integral_congr fun x hx => _
    ring_nf
  · -- now a tedious rearrangement of terms
    -- gather into a single integral, and deal with continuity subgoals:
    rw [sin_zero, cos_pi_div_two, Complex.of_real_zero, zero_pow, zero_mul, mul_zero, zero_mul,
      zero_mul, sub_zero, zero_sub, ← integral_neg, ← integral_const_mul, ← integral_const_mul, ←
      integral_sub]
    rotate_left
    · apply Continuous.intervalIntegrable
      exact
        continuous_const.mul
          ((complex.continuous_cos.comp (continuous_const.mul Complex.continuous_of_real)).mul
            ((complex.continuous_of_real.comp continuous_cos).pow n))
    · apply Continuous.intervalIntegrable
      exact
        continuous_const.mul
          ((complex.continuous_cos.comp (continuous_const.mul Complex.continuous_of_real)).mul
            ((complex.continuous_of_real.comp continuous_cos).pow (n - 2)))
    · apply Nat.sub_pos_of_lt
      exact one_lt_two.trans_le hn
    refine' integral_congr fun x hx => _
    dsimp only
    -- get rid of real trig functions and divions by 2 * z:
    rw [Complex.of_real_cos, Complex.of_real_sin, Complex.sin_sq, ← mul_div_right_comm, ←
      mul_div_right_comm, ← sub_div, mul_div, ← neg_div]
    congr 1
    have : Complex.cos ↑x ^ n = Complex.cos ↑x ^ (n - 2) * Complex.cos ↑x ^ 2 := by
      conv_lhs => rw [← Nat.sub_add_cancel hn, pow_add]
    rw [this]
    ring
  · apply Continuous.intervalIntegrable
    exact
      ((complex.continuous_of_real.comp continuous_cos).pow n).sub
        ((continuous_const.mul ((complex.continuous_of_real.comp continuous_sin).pow 2)).mul
          ((complex.continuous_of_real.comp continuous_cos).pow (n - 2)))
  · apply Continuous.intervalIntegrable
    exact complex.continuous_sin.comp (continuous_const.mul Complex.continuous_of_real)
#align euler_sine.integral_sin_mul_sin_mul_cos_pow_eq EulerSine.integral_sin_mul_sin_mul_cos_pow_eq

/-- Note this also holds for `z = 0`, but we do not need this case for `sin_pi_mul_eq`.  -/
theorem integral_cos_mul_cos_pow (hn : 2 ≤ n) (hz : z ≠ 0) :
    ((1 - 4 * z ^ 2 / n ^ 2) * ∫ x : ℝ in 0 ..π / 2, Complex.cos (2 * z * x) * cos x ^ n) =
      (n - 1 : ℂ) / n * ∫ x : ℝ in 0 ..π / 2, Complex.cos (2 * z * x) * cos x ^ (n - 2) :=
  by
  have nne : (n : ℂ) ≠ 0 := by
    contrapose! hn
    rw [Nat.cast_eq_zero] at hn
    rw [hn]
    exact zero_lt_two
  have := integral_cos_mul_cos_pow_aux hn hz
  rw [integral_sin_mul_sin_mul_cos_pow_eq hn hz, sub_eq_neg_add, mul_add, ← sub_eq_iff_eq_add] at
    this
  convert congr_arg (fun u : ℂ => -u * (2 * z) ^ 2 / n ^ 2) this using 1 <;>
    · field_simp
      ring
#align euler_sine.integral_cos_mul_cos_pow EulerSine.integral_cos_mul_cos_pow

/-- Note this also holds for `z = 0`, but we do not need this case for `sin_pi_mul_eq`. -/
theorem integral_cos_mul_cos_pow_even (n : ℕ) (hz : z ≠ 0) :
    ((1 - z ^ 2 / (n + 1) ^ 2) *
        ∫ x : ℝ in 0 ..π / 2, Complex.cos (2 * z * x) * cos x ^ (2 * n + 2)) =
      (2 * n + 1 : ℂ) / (2 * n + 2) *
        ∫ x : ℝ in 0 ..π / 2, Complex.cos (2 * z * x) * cos x ^ (2 * n) :=
  by
  convert integral_cos_mul_cos_pow (by linarith : 2 ≤ 2 * n + 2) hz using 3
  · simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_two]
    nth_rw_rhs 3 [← mul_one (2 : ℂ)]
    rw [← mul_add, mul_pow, ← div_div]
    ring
  · push_cast
    ring
  · push_cast
    ring
#align euler_sine.integral_cos_mul_cos_pow_even EulerSine.integral_cos_mul_cos_pow_even

/-- Relate the integral `cos x ^ n` over `[0, π/2]` to the integral of `sin x ^ n` over `[0, π]`,
which is studied in `data.real.pi.wallis` and other places. -/
theorem integral_cos_pow_eq (n : ℕ) :
    (∫ x : ℝ in 0 ..π / 2, cos x ^ n) = 1 / 2 * ∫ x : ℝ in 0 ..π, sin x ^ n :=
  by
  rw [mul_comm (1 / 2 : ℝ), ← div_eq_iff (one_div_ne_zero (two_ne_zero' ℝ)), ← div_mul, div_one,
    mul_two]
  have L : IntervalIntegrable _ volume 0 (π / 2) := (continuous_sin.pow n).IntervalIntegrable _ _
  have R : IntervalIntegrable _ volume (π / 2) π := (continuous_sin.pow n).IntervalIntegrable _ _
  rw [← integral_add_adjacent_intervals L R]
  congr 1
  · nth_rw 1 [(by ring : 0 = π / 2 - π / 2)]
    nth_rw 3 [(by ring : π / 2 = π / 2 - 0)]
    rw [← integral_comp_sub_left]
    refine' integral_congr fun x _ => _
    dsimp only
    rw [cos_pi_div_two_sub]
  · nth_rw 3 [(by ring : π = π / 2 + π / 2)]
    nth_rw 2 [(by ring : π / 2 = 0 + π / 2)]
    rw [← integral_comp_add_right]
    refine' integral_congr fun x _ => _
    dsimp only
    rw [sin_add_pi_div_two]
#align euler_sine.integral_cos_pow_eq EulerSine.integral_cos_pow_eq

theorem integral_cos_pow_pos (n : ℕ) : 0 < ∫ x : ℝ in 0 ..π / 2, cos x ^ n :=
  (integral_cos_pow_eq n).symm ▸ mul_pos one_half_pos (integral_sin_pow_pos _)
#align euler_sine.integral_cos_pow_pos EulerSine.integral_cos_pow_pos

/-- Finite form of Euler's sine product, with remainder term expressed as a ratio of cosine
integrals. -/
theorem sin_pi_mul_eq (z : ℂ) (n : ℕ) :
    Complex.sin (π * z) =
      ((π * z * ∏ j in Finset.range n, 1 - z ^ 2 / (j + 1) ^ 2) *
          ∫ x in 0 ..π / 2, Complex.cos (2 * z * x) * cos x ^ (2 * n)) /
        ↑(∫ x in 0 ..π / 2, cos x ^ (2 * n)) :=
  by
  rcases eq_or_ne z 0 with (rfl | hz)
  · simp
  induction' n with n hn
  · simp_rw [mul_zero, pow_zero, mul_one, Finset.prod_range_zero, mul_one, integral_one, sub_zero]
    rw [integral_cos_mul_complex (mul_ne_zero two_ne_zero hz), Complex.of_real_zero, mul_zero,
      Complex.sin_zero, zero_div, sub_zero,
      (by
        push_cast
        field_simp
        ring : 2 * z * ↑(π / 2) = π * z)]
    field_simp [complex.of_real_ne_zero.mpr pi_pos.ne']
    ring
  · rw [hn, Finset.prod_range_succ]
    set A := ∏ j in Finset.range n, 1 - z ^ 2 / (j + 1) ^ 2
    set B := ∫ x : ℝ in 0 ..π / 2, Complex.cos (2 * z * x) * cos x ^ (2 * n)
    set C := ∫ x : ℝ in 0 ..π / 2, cos x ^ (2 * n)
    have aux' : 2 * n.succ = 2 * n + 2 := by rw [Nat.succ_eq_add_one, mul_add, mul_one]
    have : (∫ x : ℝ in 0 ..π / 2, cos x ^ (2 * n.succ)) = (2 * (n : ℝ) + 1) / (2 * n + 2) * C :=
      by
      rw [integral_cos_pow_eq]
      dsimp only [C]
      rw [integral_cos_pow_eq, aux', integral_sin_pow, sin_zero, sin_pi, pow_succ, zero_mul,
        zero_mul, zero_mul, sub_zero, zero_div, zero_add, ← mul_assoc, ← mul_assoc,
        mul_comm (1 / 2 : ℝ) _, Nat.cast_mul, Nat.cast_bit0, Nat.cast_one]
    rw [this]
    change
      ↑π * z * A * B / ↑C =
        (↑π * z * (A * (1 - z ^ 2 / (↑n + 1) ^ 2)) *
            ∫ x : ℝ in 0 ..π / 2, Complex.cos (2 * z * ↑x) * ↑(cos x) ^ (2 * n.succ)) /
          ↑((2 * ↑n + 1) / (2 * ↑n + 2) * C)
    have :
      (↑π * z * (A * (1 - z ^ 2 / (↑n + 1) ^ 2)) *
          ∫ x : ℝ in 0 ..π / 2, Complex.cos (2 * z * ↑x) * ↑(cos x) ^ (2 * n.succ)) =
        ↑π * z * A *
          ((1 - z ^ 2 / ↑n.succ ^ 2) *
            ∫ x : ℝ in 0 ..π / 2, Complex.cos (2 * z * ↑x) * ↑(cos x) ^ (2 * n.succ)) :=
      by
      nth_rw_rhs 1 [Nat.succ_eq_add_one]
      rw [Nat.cast_add_one]
      ring
    rw [this]
    suffices
      ((1 - z ^ 2 / ↑n.succ ^ 2) *
          ∫ x : ℝ in 0 ..π / 2, Complex.cos (2 * z * ↑x) * ↑(cos x) ^ (2 * n.succ)) =
        (2 * n + 1) / (2 * n + 2) * B
      by
      rw [this, Complex.of_real_mul, Complex.of_real_div]
      have : (C : ℂ) ≠ 0 := complex.of_real_ne_zero.mpr (integral_cos_pow_pos _).ne'
      have : 2 * (n : ℂ) + 1 ≠ 0 :=
        by
        convert (Nat.cast_add_one_ne_zero (2 * n) : (↑(2 * n) + 1 : ℂ) ≠ 0)
        simp
      have : 2 * (n : ℂ) + 2 ≠ 0 :=
        by
        convert (Nat.cast_add_one_ne_zero (2 * n + 1) : (↑(2 * n + 1) + 1 : ℂ) ≠ 0) using 1
        push_cast
        ring
      field_simp
      ring
    convert integral_cos_mul_cos_pow_even n hz
    rw [Nat.cast_succ]
#align euler_sine.sin_pi_mul_eq EulerSine.sin_pi_mul_eq

end IntegralRecursion

end EulerSine

