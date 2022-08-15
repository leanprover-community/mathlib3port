/-
Copyright (c) 2022 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
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

theorem rpow_mul_exp_neg_mul_sq_is_o_exp_neg {b : ℝ} (hb : 0 < b) (s : ℝ) :
    (fun x : ℝ => x ^ s * exp (-b * x ^ 2)) =o[at_top] fun x : ℝ => exp (-(1 / 2) * x) := by
  apply ((is_O_refl (fun x : ℝ => x ^ s) at_top).mul_is_o (exp_neg_mul_sq_is_o_exp_neg hb)).trans
  convert Gamma_integrand_is_o s
  simp_rw [mul_comm]

theorem integrable_on_rpow_mul_exp_neg_mul_sq {b : ℝ} (hb : 0 < b) {s : ℝ} (hs : -1 < s) :
    IntegrableOn (fun x : ℝ => x ^ s * exp (-b * x ^ 2)) (Ioi 0) := by
  rw [← Ioc_union_Ioi_eq_Ioi (zero_le_one : (0 : ℝ) ≤ 1), integrable_on_union]
  constructor
  · rw [← integrable_on_Icc_iff_integrable_on_Ioc]
    refine' integrable_on.mul_continuous_on _ _ is_compact_Icc
    · refine' (interval_integrable_iff_integrable_Icc_of_le zero_le_one).mp _
      exact intervalIntegral.interval_integrable_rpow' hs
      
    · exact (continuous_exp.comp (continuous_const.mul (continuous_pow 2))).ContinuousOn
      
    
  · have B : (0 : ℝ) < 1 / 2 := by
      norm_num
    apply integrable_of_is_O_exp_neg B _ (is_o.is_O (rpow_mul_exp_neg_mul_sq_is_o_exp_neg hb _))
    intro x hx
    have N : x ≠ 0 := by
      refine' (zero_lt_one.trans_le _).ne'
      exact hx
    apply ((continuous_at_rpow_const _ _ (Or.inl N)).mul _).ContinuousWithinAt
    exact (continuous_exp.comp (continuous_const.mul (continuous_pow 2))).ContinuousAt
    

theorem integrable_rpow_mul_exp_neg_mul_sq {b : ℝ} (hb : 0 < b) {s : ℝ} (hs : -1 < s) :
    Integrable fun x : ℝ => x ^ s * exp (-b * x ^ 2) := by
  rw [← integrable_on_univ, ← @Iio_union_Ici _ _ (0 : ℝ), integrable_on_union, integrable_on_Ici_iff_integrable_on_Ioi]
  refine' ⟨_, integrable_on_rpow_mul_exp_neg_mul_sq hb hs⟩
  rw [←
    (measure.measure_preserving_neg (volume : Measureₓ ℝ)).integrable_on_comp_preimage
      (Homeomorph.neg ℝ).toMeasurableEquiv.MeasurableEmbedding]
  simp only [← Function.comp, ← neg_sq, ← neg_preimage, ← preimage_neg_Iio, ← neg_negₓ, ← neg_zero]
  apply integrable.mono' (integrable_on_rpow_mul_exp_neg_mul_sq hb hs)
  · apply Measurable.ae_strongly_measurable
    exact (measurable_id'.neg.pow measurable_const).mul ((measurable_id'.pow measurable_const).const_mul (-b)).exp
    
  · have : MeasurableSet (Ioi (0 : ℝ)) := measurable_set_Ioi
    filter_upwards [ae_restrict_mem this] with x hx
    have h'x : 0 ≤ x := le_of_ltₓ hx
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (exp_pos _).le]
    apply mul_le_mul_of_nonneg_right _ (exp_pos _).le
    simpa [← abs_of_nonneg h'x] using abs_rpow_le_abs_rpow (-x) s
    

theorem integrable_exp_neg_mul_sq {b : ℝ} (hb : 0 < b) : Integrable fun x : ℝ => exp (-b * x ^ 2) := by
  have A : (-1 : ℝ) < 0 := by
    norm_num
  convert integrable_rpow_mul_exp_neg_mul_sq hb A
  simp

theorem integrable_exp_neg_mul_sq_iff {b : ℝ} : (Integrable fun x : ℝ => exp (-b * x ^ 2)) ↔ 0 < b := by
  refine' ⟨fun h => _, integrable_exp_neg_mul_sq⟩
  by_contra' hb
  have : (∫⁻ x : ℝ, 1) ≤ ∫⁻ x : ℝ, ∥exp (-b * x ^ 2)∥₊ := by
    apply lintegral_mono fun x => _
    simp only [← neg_mul, ← Ennreal.one_le_coe_iff, to_nnreal_one, ← to_nnreal_le_iff_le_coe, ←
      Real.norm_of_nonneg (exp_pos _).le, ← coe_nnnorm, ← one_le_exp_iff, ← Right.nonneg_neg_iff]
    exact mul_nonpos_of_nonpos_of_nonneg hb (sq_nonneg _)
  simpa using this.trans_lt h.2

theorem integrable_mul_exp_neg_mul_sq {b : ℝ} (hb : 0 < b) : Integrable fun x : ℝ => x * exp (-b * x ^ 2) := by
  have A : (-1 : ℝ) < 1 := by
    norm_num
  convert integrable_rpow_mul_exp_neg_mul_sq hb A
  simp

theorem integral_mul_exp_neg_mul_sq {b : ℝ} (hb : 0 < b) : (∫ r in Ioi 0, r * exp (-b * r ^ 2)) = (2 * b)⁻¹ := by
  have I : integrable fun x => x * exp (-b * x ^ 2) := integrable_mul_exp_neg_mul_sq hb
  refine' tendsto_nhds_unique (interval_integral_tendsto_integral_Ioi _ I.integrable_on Filter.tendsto_id) _
  have A : ∀ x, HasDerivAt (fun x => -(2 * b)⁻¹ * exp (-b * x ^ 2)) (x * exp (-b * x ^ 2)) x := by
    intro x
    convert ((has_deriv_at_pow 2 x).const_mul (-b)).exp.const_mul (-(2 * b)⁻¹) using 1
    field_simp [← hb.ne']
    ring
  have :
    ∀ y : ℝ, (∫ x in 0 ..id y, x * exp (-b * x ^ 2)) = -(2 * b)⁻¹ * exp (-b * y ^ 2) - -(2 * b)⁻¹ * exp (-b * 0 ^ 2) :=
    fun y => intervalIntegral.integral_eq_sub_of_has_deriv_at (fun x hx => A x) I.interval_integrable
  simp_rw [this]
  have L : tendsto (fun x : ℝ => (2 * b)⁻¹ - (2 * b)⁻¹ * exp (-b * x ^ 2)) at_top (𝓝 ((2 * b)⁻¹ - (2 * b)⁻¹ * 0)) := by
    refine' tendsto_const_nhds.sub _
    apply tendsto.const_mul
    apply tendsto_exp_at_bot.comp
    exact tendsto.neg_const_mul_at_top (neg_lt_zero.2 hb) (tendsto_pow_at_top two_ne_zero)
  simpa using L

theorem integral_gaussian (b : ℝ) : (∫ x, exp (-b * x ^ 2)) = sqrt (π / b) := by
  -- First we deal with the crazy case where `b ≤ 0`: then both sides vanish.
  rcases le_or_ltₓ b 0 with (hb | hb)
  · rw [integral_undef, sqrt_eq_zero_of_nonpos]
    · exact div_nonpos_of_nonneg_of_nonpos pi_pos.le hb
      
    · simpa only [← not_ltₓ, ← integrable_exp_neg_mul_sq_iff] using hb
      
    
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
      simp only [Real.exp_add, ← neg_add_rev, ← Real.exp_eq_exp]
      ring
    _ = ∫ p in polar_coord.target, p.1 * exp (-b * ((p.1 * cos p.2) ^ 2 + (p.1 * sin p.2) ^ 2)) :=
      (integral_comp_polar_coord_symm fun p => exp (-b * (p.1 ^ 2 + p.2 ^ 2))).symm
    _ = (∫ r in Ioi (0 : ℝ), r * exp (-b * r ^ 2)) * ∫ θ in Ioo (-π) π, 1 := by
      rw [← set_integral_prod_mul]
      congr with p
      rw [mul_oneₓ]
      congr
      conv_rhs => rw [← one_mulₓ (p.1 ^ 2), ← sin_sq_add_cos_sq p.2]
      ring_exp
    _ = π / b := by
      have : 0 ≤ π + π := by
        linarith [Real.pi_pos]
      simp only [← integral_const, ← measure.restrict_apply', ← measurable_set_Ioo, ← univ_inter, ← this, ←
        sub_neg_eq_add, ← Algebra.id.smul_eq_mul, ← mul_oneₓ, ← volume_Ioo, ← two_mul, ← Ennreal.to_real_of_real, ←
        integral_mul_exp_neg_mul_sq hb, ← one_mulₓ]
      field_simp [← hb.ne']
      ring
    _ = sqrt (π / b) ^ 2 := by
      rw [sq_sqrt]
      exact div_nonneg pi_pos.le hb.le
    

