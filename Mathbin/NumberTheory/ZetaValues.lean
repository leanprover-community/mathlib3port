/-
Copyright (c) 2022 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler

! This file was ported from Lean 3 source module number_theory.zeta_values
! leanprover-community/mathlib commit 7c523cb78f4153682c2929e3006c863bfef463d0
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.NumberTheory.BernoulliPolynomials
import Mathbin.Analysis.SpecialFunctions.Integrals
import Mathbin.MeasureTheory.Integral.IntervalIntegral
import Mathbin.Analysis.Fourier.AddCircle

/-!
# Critical values of the Riemann zeta function

In this file we evaluate the Fourier coefficients of Bernoulli polynomials on the interval `[0, 1]`.
In a future iteration this will be used to evaluate critical values of the Riemann zeta function
(and other Dirichlet L-functions).
-/


noncomputable section

open Nat Real Interval

open Complex MeasureTheory Set intervalIntegral

section BernoulliFunProps

/-! Simple properties of the Bernoulli polynomial, as a function `ℝ → ℝ`. -/


/-- The function `x ↦ Bₖ(x) : ℝ → ℝ`. -/
def bernoulliFun (k : ℕ) (x : ℝ) : ℝ :=
  (Polynomial.map (algebraMap ℚ ℝ) (Polynomial.bernoulli k)).eval x
#align bernoulli_fun bernoulliFun

theorem bernoulli_fun_eval_zero (k : ℕ) : bernoulliFun k 0 = bernoulli k := by
  rw [bernoulliFun, Polynomial.eval_zero_map, Polynomial.bernoulli_eval_zero, eq_ratCast]
#align bernoulli_fun_eval_zero bernoulli_fun_eval_zero

theorem bernoulli_fun_endpoints_eq_of_ne_one {k : ℕ} (hk : k ≠ 1) :
    bernoulliFun k 1 = bernoulliFun k 0 := by
  rw [bernoulli_fun_eval_zero, bernoulliFun, Polynomial.eval_one_map, Polynomial.bernoulli_eval_one,
    bernoulli_eq_bernoulli'_of_ne_one hk, eq_ratCast]
#align bernoulli_fun_endpoints_eq_of_ne_one bernoulli_fun_endpoints_eq_of_ne_one

theorem bernoulli_fun_eval_one (k : ℕ) : bernoulliFun k 1 = bernoulliFun k 0 + ite (k = 1) 1 0 :=
  by
  rw [bernoulliFun, bernoulli_fun_eval_zero, Polynomial.eval_one_map, Polynomial.bernoulli_eval_one]
  split_ifs
  · rw [h, bernoulli_one, bernoulli'_one, eq_ratCast]
    push_cast
    ring
  · rw [bernoulli_eq_bernoulli'_of_ne_one h, add_zero, eq_ratCast]
#align bernoulli_fun_eval_one bernoulli_fun_eval_one

theorem has_deriv_at_bernoulli_fun (k : ℕ) (x : ℝ) :
    HasDerivAt (bernoulliFun k) (k * bernoulliFun (k - 1) x) x :=
  by
  convert ((Polynomial.bernoulli k).map <| algebraMap ℚ ℝ).HasDerivAt x using 1
  simp only [bernoulliFun, Polynomial.derivative_map, Polynomial.derivative_bernoulli k,
    Polynomial.map_mul, Polynomial.map_nat_cast, Polynomial.eval_mul, Polynomial.eval_nat_cast]
#align has_deriv_at_bernoulli_fun has_deriv_at_bernoulli_fun

theorem antideriv_bernoulli_fun (k : ℕ) (x : ℝ) :
    HasDerivAt (fun x => bernoulliFun (k + 1) x / (k + 1)) (bernoulliFun k x) x :=
  by
  convert (has_deriv_at_bernoulli_fun (k + 1) x).div_const _
  field_simp [Nat.cast_add_one_ne_zero k]
  ring
#align antideriv_bernoulli_fun antideriv_bernoulli_fun

theorem integral_bernoulli_fun_eq_zero {k : ℕ} (hk : k ≠ 0) :
    (∫ x : ℝ in 0 ..1, bernoulliFun k x) = 0 :=
  by
  rw [integral_eq_sub_of_has_deriv_at (fun x hx => antideriv_bernoulli_fun k x)
      ((Polynomial.continuous _).IntervalIntegrable _ _)]
  dsimp only
  rw [bernoulli_fun_eval_one]
  split_ifs
  · exfalso
    exact hk (nat.succ_inj'.mp h); · simp
#align integral_bernoulli_fun_eq_zero integral_bernoulli_fun_eq_zero

end BernoulliFunProps

section BernoulliFourierCoeffs

/-! Compute the Fourier coefficients of the Bernoulli functions via integration by parts. -/


attribute [local instance] Real.fact_zero_lt_one

/-- The `n`-th Fourier coefficient of the `k`-th Bernoulli function on the interval `[0, 1]`. -/
def bernoulliFourierCoeff (k : ℕ) (n : ℤ) : ℂ :=
  fourierCoeffOn zero_lt_one (fun x => bernoulliFun k x) n
#align bernoulli_fourier_coeff bernoulliFourierCoeff

/-- Recurrence relation (in `k`) for the `n`-th Fourier coefficient of `Bₖ`. -/
theorem bernoulli_fourier_coeff_recurrence (k : ℕ) {n : ℤ} (hn : n ≠ 0) :
    bernoulliFourierCoeff k n =
      1 / (-2 * π * I * n) * (ite (k = 1) 1 0 - k * bernoulliFourierCoeff (k - 1) n) :=
  by
  unfold bernoulliFourierCoeff
  rw [fourier_coeff_on_of_has_deriv_at zero_lt_one hn
      (fun x hx => (has_deriv_at_bernoulli_fun k x).of_real_comp)
      ((continuous_of_real.comp <|
            continuous_const.mul <| Polynomial.continuous _).IntervalIntegrable
        _ _)]
  dsimp only
  simp_rw [of_real_one, of_real_zero, sub_zero, one_mul]
  rw [QuotientAddGroup.coe_zero, fourier_eval_zero, one_mul, ← of_real_sub, bernoulli_fun_eval_one,
    add_sub_cancel']
  congr 2
  · split_ifs
    all_goals simp only [of_real_one, of_real_zero, one_mul]
  · simp_rw [of_real_mul, of_real_nat_cast, fourierCoeffOn.const_mul]
#align bernoulli_fourier_coeff_recurrence bernoulli_fourier_coeff_recurrence

/-- The Fourier coefficients of `B₀(x) = 1`. -/
theorem bernoulli_zero_fourier_coeff {n : ℤ} (hn : n ≠ 0) : bernoulliFourierCoeff 0 n = 0 := by
  simpa using bernoulli_fourier_coeff_recurrence 0 hn
#align bernoulli_zero_fourier_coeff bernoulli_zero_fourier_coeff

/-- The `0`-th Fourier coefficient of `Bₖ(x)`. -/
theorem bernoulli_fourier_coeff_zero {k : ℕ} (hk : k ≠ 0) : bernoulliFourierCoeff k 0 = 0 := by
  simp_rw [bernoulliFourierCoeff, fourier_coeff_on_eq_integral, neg_zero, fourier_zero, sub_zero,
    div_one, one_smul, intervalIntegral.integral_of_real, integral_bernoulli_fun_eq_zero hk,
    of_real_zero]
#align bernoulli_fourier_coeff_zero bernoulli_fourier_coeff_zero

theorem bernoulli_fourier_coeff_eq {k : ℕ} (hk : k ≠ 0) (n : ℤ) :
    bernoulliFourierCoeff k n = -k ! / (2 * π * I * n) ^ k :=
  by
  rcases eq_or_ne n 0 with (rfl | hn)
  · rw [bernoulli_fourier_coeff_zero hk, Int.cast_zero, mul_zero, zero_pow' _ hk, div_zero]
  refine' Nat.le_induction _ (fun k hk h'k => _) k (nat.one_le_iff_ne_zero.mpr hk)
  · rw [bernoulli_fourier_coeff_recurrence 1 hn]
    simp only [Nat.cast_one, tsub_self, neg_mul, one_mul, eq_self_iff_true, if_true,
      Nat.factorial_one, pow_one, inv_I, mul_neg]
    rw [bernoulli_zero_fourier_coeff hn, sub_zero, mul_one, div_neg, neg_div]
  · rw [bernoulli_fourier_coeff_recurrence (k + 1) hn, Nat.add_sub_cancel k 1]
    split_ifs
    · exfalso
      exact (ne_of_gt (nat.lt_succ_iff.mpr hk)) h
    · rw [h'k, Nat.factorial_succ, zero_sub, Nat.cast_mul, pow_add, pow_one, neg_div, mul_neg,
        mul_neg, mul_neg, neg_neg, neg_mul, neg_mul, neg_mul, div_neg]
      field_simp [int.cast_ne_zero.mpr hn, I_ne_zero]
      ring_nf
#align bernoulli_fourier_coeff_eq bernoulli_fourier_coeff_eq

end BernoulliFourierCoeffs

