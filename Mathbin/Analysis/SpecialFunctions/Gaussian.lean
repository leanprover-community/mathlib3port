/-
Copyright (c) 2022 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel

! This file was ported from Lean 3 source module analysis.special_functions.gaussian
! leanprover-community/mathlib commit 0743cc5d9d86bcd1bba10f480e948a257d65056f
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Analysis.SpecialFunctions.Gamma
import Mathbin.Analysis.SpecialFunctions.PolarCoord

/-!
# Gaussian integral

We prove the formula `∫ x, exp (-b * x^2) = sqrt (π / b)`, in `integral_gaussian`.
-/


noncomputable section

open Real Set MeasureTheory Filter Asymptotics

open Real TopologicalSpace

theorem exp_neg_mul_sq_is_o_exp_neg {b : ℝ} (hb : 0 < b) :
    (fun x : ℝ => exp (-b * x ^ 2)) =o[at_top] fun x : ℝ => exp (-x) := by
  have A : (fun x : ℝ => -x - -b * x ^ 2) = fun x => x * (b * x + -1) := by
    ext x
    ring
  rw [is_o_exp_comp_exp_comp, A]
  apply tendsto.at_top_mul_at_top tendsto_id
  apply tendsto_at_top_add_const_right at_top (-1 : ℝ)
  exact tendsto.const_mul_at_top hb tendsto_id
#align exp_neg_mul_sq_is_o_exp_neg exp_neg_mul_sq_is_o_exp_neg

theorem rpow_mul_exp_neg_mul_sq_is_o_exp_neg {b : ℝ} (hb : 0 < b) (s : ℝ) :
    (fun x : ℝ => x ^ s * exp (-b * x ^ 2)) =o[at_top] fun x : ℝ => exp (-(1 / 2) * x) := by
  apply ((is_O_refl (fun x : ℝ => x ^ s) at_top).mul_is_o (exp_neg_mul_sq_is_o_exp_neg hb)).trans
  convert Gamma_integrand_is_o s
  simp_rw [mul_comm]
#align rpow_mul_exp_neg_mul_sq_is_o_exp_neg rpow_mul_exp_neg_mul_sq_is_o_exp_neg

theorem integrableOnRpowMulExpNegMulSq {b : ℝ} (hb : 0 < b) {s : ℝ} (hs : -1 < s) :
    IntegrableOn (fun x : ℝ => x ^ s * exp (-b * x ^ 2)) (Ioi 0) := by
  rw [← Ioc_union_Ioi_eq_Ioi (zero_le_one : (0 : ℝ) ≤ 1), integrable_on_union]
  constructor
  · rw [← integrable_on_Icc_iff_integrable_on_Ioc]
    refine' integrable_on.mul_continuous_on _ _ is_compact_Icc
    · refine' (interval_integrable_iff_integrable_Icc_of_le zero_le_one).mp _
      exact intervalIntegral.intervalIntegrableRpow' hs
    · exact (continuous_exp.comp (continuous_const.mul (continuous_pow 2))).ContinuousOn
  · have B : (0 : ℝ) < 1 / 2 := by norm_num
    apply integrableOfIsOExpNeg B _ (is_o.is_O (rpow_mul_exp_neg_mul_sq_is_o_exp_neg hb _))
    intro x hx
    have N : x ≠ 0 := by 
      refine' (zero_lt_one.trans_le _).ne'
      exact hx
    apply ((continuous_at_rpow_const _ _ (Or.inl N)).mul _).ContinuousWithinAt
    exact (continuous_exp.comp (continuous_const.mul (continuous_pow 2))).ContinuousAt
#align integrable_on_rpow_mul_exp_neg_mul_sq integrableOnRpowMulExpNegMulSq

theorem integrableRpowMulExpNegMulSq {b : ℝ} (hb : 0 < b) {s : ℝ} (hs : -1 < s) :
    Integrable fun x : ℝ => x ^ s * exp (-b * x ^ 2) := by
  rw [← integrable_on_univ, ← @Iio_union_Ici _ _ (0 : ℝ), integrable_on_union,
    integrable_on_Ici_iff_integrable_on_Ioi]
  refine' ⟨_, integrableOnRpowMulExpNegMulSq hb hs⟩
  rw [←
    (measure.measure_preserving_neg (volume : Measure ℝ)).integrable_on_comp_preimage
      (Homeomorph.neg ℝ).toMeasurableEquiv.MeasurableEmbedding]
  simp only [Function.comp, neg_sq, neg_preimage, preimage_neg_Iio, neg_neg, neg_zero]
  apply integrable.mono' (integrableOnRpowMulExpNegMulSq hb hs)
  · apply Measurable.aeStronglyMeasurable
    exact
      (measurable_id'.neg.pow measurableConst).mul
        ((measurable_id'.pow measurableConst).const_mul (-b)).exp
  · have : MeasurableSet (Ioi (0 : ℝ)) := measurableSetIoi
    filter_upwards [ae_restrict_mem this] with x hx
    have h'x : 0 ≤ x := le_of_lt hx
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (exp_pos _).le]
    apply mul_le_mul_of_nonneg_right _ (exp_pos _).le
    simpa [abs_of_nonneg h'x] using abs_rpow_le_abs_rpow (-x) s
#align integrable_rpow_mul_exp_neg_mul_sq integrableRpowMulExpNegMulSq

theorem integrableExpNegMulSq {b : ℝ} (hb : 0 < b) : Integrable fun x : ℝ => exp (-b * x ^ 2) := by
  have A : (-1 : ℝ) < 0 := by norm_num
  convert integrableRpowMulExpNegMulSq hb A
  simp
#align integrable_exp_neg_mul_sq integrableExpNegMulSq

theorem integrable_on_Ioi_exp_neg_mul_sq_iff {b : ℝ} :
    IntegrableOn (fun x : ℝ => exp (-b * x ^ 2)) (Ioi 0) ↔ 0 < b := by
  refine' ⟨fun h => _, fun h => (integrableExpNegMulSq h).IntegrableOn⟩
  by_contra' hb
  have : (∫⁻ x : ℝ in Ioi 0, 1) ≤ ∫⁻ x : ℝ in Ioi 0, ‖exp (-b * x ^ 2)‖₊ := by
    apply lintegral_mono fun x => _
    simp only [neg_mul, Ennreal.one_le_coe_iff, ← to_nnreal_one, to_nnreal_le_iff_le_coe,
      Real.norm_of_nonneg (exp_pos _).le, coe_nnnorm, one_le_exp_iff, Right.nonneg_neg_iff]
    exact mul_nonpos_of_nonpos_of_nonneg hb (sq_nonneg _)
  simpa using this.trans_lt h.2
#align integrable_on_Ioi_exp_neg_mul_sq_iff integrable_on_Ioi_exp_neg_mul_sq_iff

theorem integrable_exp_neg_mul_sq_iff {b : ℝ} :
    (Integrable fun x : ℝ => exp (-b * x ^ 2)) ↔ 0 < b :=
  ⟨fun h => integrable_on_Ioi_exp_neg_mul_sq_iff.mp h.IntegrableOn, integrableExpNegMulSq⟩
#align integrable_exp_neg_mul_sq_iff integrable_exp_neg_mul_sq_iff

theorem integrableMulExpNegMulSq {b : ℝ} (hb : 0 < b) :
    Integrable fun x : ℝ => x * exp (-b * x ^ 2) := by
  have A : (-1 : ℝ) < 1 := by norm_num
  convert integrableRpowMulExpNegMulSq hb A
  simp
#align integrable_mul_exp_neg_mul_sq integrableMulExpNegMulSq

theorem integral_mul_exp_neg_mul_sq {b : ℝ} (hb : 0 < b) :
    (∫ r in Ioi 0, r * exp (-b * r ^ 2)) = (2 * b)⁻¹ := by
  have I : integrable fun x => x * exp (-b * x ^ 2) := integrableMulExpNegMulSq hb
  refine'
    tendsto_nhds_unique (interval_integral_tendsto_integral_Ioi _ I.integrable_on Filter.tendsto_id)
      _
  have A : ∀ x, HasDerivAt (fun x => -(2 * b)⁻¹ * exp (-b * x ^ 2)) (x * exp (-b * x ^ 2)) x := by
    intro x
    convert ((hasDerivAtPow 2 x).const_mul (-b)).exp.const_mul (-(2 * b)⁻¹) using 1
    field_simp [hb.ne']
    ring
  have :
    ∀ y : ℝ,
      (∫ x in 0 ..id y, x * exp (-b * x ^ 2)) =
        -(2 * b)⁻¹ * exp (-b * y ^ 2) - -(2 * b)⁻¹ * exp (-b * 0 ^ 2) :=
    fun y =>
    intervalIntegral.integral_eq_sub_of_has_deriv_at (fun x hx => A x) I.interval_integrable
  simp_rw [this]
  have L :
    tendsto (fun x : ℝ => (2 * b)⁻¹ - (2 * b)⁻¹ * exp (-b * x ^ 2)) at_top
      (𝓝 ((2 * b)⁻¹ - (2 * b)⁻¹ * 0)) :=
    by 
    refine' tendsto_const_nhds.sub _
    apply tendsto.const_mul
    apply tendsto_exp_at_bot.comp
    exact tendsto.neg_const_mul_at_top (neg_lt_zero.2 hb) (tendsto_pow_at_top two_ne_zero)
  simpa using L
#align integral_mul_exp_neg_mul_sq integral_mul_exp_neg_mul_sq

theorem integral_gaussian (b : ℝ) : (∫ x, exp (-b * x ^ 2)) = sqrt (π / b) :=
  by
  -- First we deal with the crazy case where `b ≤ 0`: then both sides vanish.
  rcases le_or_lt b 0 with (hb | hb)
  · rw [integral_undef, sqrt_eq_zero_of_nonpos]
    · exact div_nonpos_of_nonneg_of_nonpos pi_pos.le hb
    · simpa only [not_lt, integrable_exp_neg_mul_sq_iff] using hb
  -- Assume now `b > 0`. We will show that the squares of the sides coincide.
  refine' (sq_eq_sq _ (sqrt_nonneg _)).1 _
  · exact integral_nonneg fun x => (exp_pos _).le
  /- We compute `(∫ exp(-b x^2))^2` as an integral over `ℝ^2`, and then make a polar change of
    coordinates. We are left with `∫ r * exp (-b r^2)`, which has been computed in
    `integral_mul_exp_neg_mul_sq` using the fact that this function has an obvious primitive. -/
  calc
    (∫ x, Real.exp (-b * x ^ 2)) ^ 2 = ∫ p : ℝ × ℝ, exp (-b * p.1 ^ 2) * exp (-b * p.2 ^ 2) := by
      rw [pow_two, ← integral_prod_mul]
      rfl
    _ = ∫ p : ℝ × ℝ, Real.exp (-b * (p.1 ^ 2 + p.2 ^ 2)) := by
      congr
      ext p
      simp only [← Real.exp_add, neg_add_rev, Real.exp_eq_exp]
      ring
    _ = ∫ p in polar_coord.target, p.1 * exp (-b * ((p.1 * cos p.2) ^ 2 + (p.1 * sin p.2) ^ 2)) :=
      (integral_comp_polar_coord_symm fun p => exp (-b * (p.1 ^ 2 + p.2 ^ 2))).symm
    _ = (∫ r in Ioi (0 : ℝ), r * exp (-b * r ^ 2)) * ∫ θ in Ioo (-π) π, 1 := by
      rw [← set_integral_prod_mul]
      congr with p
      rw [mul_one]
      congr
      conv_rhs => rw [← one_mul (p.1 ^ 2), ← sin_sq_add_cos_sq p.2]
      ring
    _ = π / b := by 
      have : 0 ≤ π + π := by linarith [Real.pi_pos]
      simp only [integral_const, measure.restrict_apply', measurableSetIoo, univ_inter, this,
        sub_neg_eq_add, Algebra.id.smul_eq_mul, mul_one, volume_Ioo, two_mul,
        Ennreal.to_real_of_real, integral_mul_exp_neg_mul_sq hb, one_mul]
      field_simp [hb.ne']
      ring
    _ = sqrt (π / b) ^ 2 := by 
      rw [sq_sqrt]
      exact div_nonneg pi_pos.le hb.le
    
#align integral_gaussian integral_gaussian

open Interval

-- The Gaussian integral on the half-line, `∫ x in Ioi 0, exp (-b * x^2)`.
theorem integral_gaussian_Ioi (b : ℝ) : (∫ x in Ioi 0, exp (-b * x ^ 2)) = sqrt (π / b) / 2 := by
  rcases le_or_lt b 0 with (hb | hb)
  · rw [integral_undef, sqrt_eq_zero_of_nonpos, zero_div]
    exact div_nonpos_of_nonneg_of_nonpos pi_pos.le hb
    rwa [← integrable_on, integrable_on_Ioi_exp_neg_mul_sq_iff, not_lt]
  have full_integral := integral_gaussian b
  have : MeasurableSet (Ioi (0 : ℝ)) := measurableSetIoi
  rw [← integral_add_compl this (integrableExpNegMulSq hb), compl_Ioi] at full_integral
  suffices (∫ x in Iic 0, exp (-b * x ^ 2)) = ∫ x in Ioi 0, exp (-b * x ^ 2) by
    rw [this, ← mul_two] at full_integral
    rwa [eq_div_iff]
    exact two_ne_zero
  have : ∀ c : ℝ, (∫ x in 0 ..c, exp (-b * x ^ 2)) = ∫ x in -c..0, exp (-b * x ^ 2) := by
    intro c
    have := @intervalIntegral.integral_comp_sub_left _ _ _ _ 0 c (fun x => exp (-b * x ^ 2)) 0
    simpa [zero_sub, neg_sq, neg_zero] using this
  have t1 :=
    interval_integral_tendsto_integral_Ioi _ (integrableExpNegMulSq hb).IntegrableOn tendsto_id
  have t2 :
    tendsto (fun c : ℝ => ∫ x in 0 ..c, exp (-b * x ^ 2)) at_top
      (𝓝 (∫ x in Iic 0, exp (-b * x ^ 2))) :=
    by 
    simp_rw [this]
    refine' interval_integral_tendsto_integral_Iic _ _ tendsto_neg_at_top_at_bot
    apply (integrableExpNegMulSq hb).IntegrableOn
  exact tendsto_nhds_unique t2 t1
#align integral_gaussian_Ioi integral_gaussian_Ioi

namespace Complex

/-- The special-value formula `Γ(1/2) = √π`, which is equivalent to the Gaussian integral. -/
theorem Gamma_one_half_eq : gamma (1 / 2) = sqrt π :=
  by
  -- first reduce to real integrals
  have hh : (1 / 2 : ℂ) = ↑(1 / 2 : ℝ) := by
    simp only [one_div, of_real_inv, of_real_bit0, of_real_one]
  have hh2 : (1 / 2 : ℂ).re = 1 / 2 := by convert Complex.of_real_re (1 / 2 : ℝ)
  replace hh2 : 0 < (1 / 2 : ℂ).re := by 
    rw [hh2]
    exact one_half_pos
  rw [Gamma_eq_integral _ hh2, hh, Gamma_integral_of_real, of_real_inj, Real.gammaIntegral]
  -- now do change-of-variables
  rw [← integral_comp_rpow_Ioi_of_pos zero_lt_two]
  have :
    eq_on
      (fun x : ℝ =>
        (2 * x ^ ((2 : ℝ) - 1)) • (Real.exp (-x ^ (2 : ℝ)) * (x ^ (2 : ℝ)) ^ (1 / (2 : ℝ) - 1)))
      (fun x : ℝ => 2 * Real.exp (-1 * x ^ (2 : ℕ))) (Ioi 0) :=
    by 
    intro x hx
    dsimp only
    have : (x ^ (2 : ℝ)) ^ (1 / (2 : ℝ) - 1) = x⁻¹ := by
      rw [← rpow_mul (le_of_lt hx)]
      norm_num
      rw [rpow_neg (le_of_lt hx), rpow_one]
    rw [smul_eq_mul, this]
    field_simp [(ne_of_lt hx).symm]
    norm_num
    ring
  rw [set_integral_congr measurableSetIoi this, integral_mul_left, integral_gaussian_Ioi]
  field_simp
  ring
#align complex.Gamma_one_half_eq Complex.Gamma_one_half_eq

end Complex

