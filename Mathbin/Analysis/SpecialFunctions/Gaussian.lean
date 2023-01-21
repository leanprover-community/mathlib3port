/-
Copyright (c) 2022 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel

! This file was ported from Lean 3 source module analysis.special_functions.gaussian
! leanprover-community/mathlib commit 2445c98ae4b87eabebdde552593519b9b6dc350c
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Analysis.SpecialFunctions.Gamma
import Mathbin.Analysis.SpecialFunctions.PolarCoord
import Mathbin.Analysis.Convex.Complex

/-!
# Gaussian integral

We prove various versions of the formula for the Gaussian integral:
* `integral_gaussian`: for real `b` we have `∫ x:ℝ, exp (-b * x^2) = sqrt (π / b)`.
* `integral_gaussian_complex`: for complex `b` with `0 < re b` we have
  `∫ x:ℝ, exp (-b * x^2) = (π / b) ^ (1 / 2)`.
* `integral_gaussian_Ioi` and `integral_gaussian_complex_Ioi`: variants for integrals over `Ioi 0`.
* `complex.Gamma_one_half_eq`: the formula `Γ (1 / 2) = √π`.
-/


noncomputable section

open Real Set MeasureTheory Filter Asymptotics

open Real TopologicalSpace

open Complex hiding exp continuous_exp abs_of_nonneg

-- mathport name: exprcexp
notation "cexp" => Complex.exp

theorem exp_neg_mul_sq_isO_exp_neg {b : ℝ} (hb : 0 < b) :
    (fun x : ℝ => exp (-b * x ^ 2)) =o[at_top] fun x : ℝ => exp (-x) :=
  by
  have A : (fun x : ℝ => -x - -b * x ^ 2) = fun x => x * (b * x + -1) :=
    by
    ext x
    ring
  rw [is_o_exp_comp_exp_comp, A]
  apply tendsto.at_top_mul_at_top tendsto_id
  apply tendsto_at_top_add_const_right at_top (-1 : ℝ)
  exact tendsto.const_mul_at_top hb tendsto_id
#align exp_neg_mul_sq_is_o_exp_neg exp_neg_mul_sq_isO_exp_neg

theorem rpow_mul_exp_neg_mul_sq_isO_exp_neg {b : ℝ} (hb : 0 < b) (s : ℝ) :
    (fun x : ℝ => x ^ s * exp (-b * x ^ 2)) =o[at_top] fun x : ℝ => exp (-(1 / 2) * x) :=
  by
  apply ((is_O_refl (fun x : ℝ => x ^ s) at_top).mul_is_o (exp_neg_mul_sq_isO_exp_neg hb)).trans
  convert Gamma_integrand_is_o s
  simp_rw [mul_comm]
#align rpow_mul_exp_neg_mul_sq_is_o_exp_neg rpow_mul_exp_neg_mul_sq_isO_exp_neg

theorem integrableOnRpowMulExpNegMulSq {b : ℝ} (hb : 0 < b) {s : ℝ} (hs : -1 < s) :
    IntegrableOn (fun x : ℝ => x ^ s * exp (-b * x ^ 2)) (Ioi 0) :=
  by
  rw [← Ioc_union_Ioi_eq_Ioi (zero_le_one : (0 : ℝ) ≤ 1), integrable_on_union]
  constructor
  · rw [← integrableOn_icc_iff_integrableOn_ioc]
    refine' integrable_on.mul_continuous_on _ _ is_compact_Icc
    · refine' (intervalIntegrable_iff_integrable_icc_of_le zero_le_one).mp _
      exact intervalIntegral.intervalIntegrableRpow' hs
    · exact (continuous_exp.comp (continuous_const.mul (continuous_pow 2))).ContinuousOn
  · have B : (0 : ℝ) < 1 / 2 := by norm_num
    apply integrableOfIsOExpNeg B _ (is_o.is_O (rpow_mul_exp_neg_mul_sq_isO_exp_neg hb _))
    intro x hx
    have N : x ≠ 0 := by
      refine' (zero_lt_one.trans_le _).ne'
      exact hx
    apply ((continuous_at_rpow_const _ _ (Or.inl N)).mul _).ContinuousWithinAt
    exact (continuous_exp.comp (continuous_const.mul (continuous_pow 2))).ContinuousAt
#align integrable_on_rpow_mul_exp_neg_mul_sq integrableOnRpowMulExpNegMulSq

theorem integrableRpowMulExpNegMulSq {b : ℝ} (hb : 0 < b) {s : ℝ} (hs : -1 < s) :
    Integrable fun x : ℝ => x ^ s * exp (-b * x ^ 2) :=
  by
  rw [← integrable_on_univ, ← @Iio_union_Ici _ _ (0 : ℝ), integrable_on_union,
    integrableOn_ici_iff_integrableOn_ioi]
  refine' ⟨_, integrableOnRpowMulExpNegMulSq hb hs⟩
  rw [←
    (measure.measure_preserving_neg (volume : Measure ℝ)).integrable_on_comp_preimage
      (Homeomorph.neg ℝ).toMeasurableEquiv.MeasurableEmbedding]
  simp only [Function.comp, neg_sq, neg_preimage, preimage_neg_Iio, neg_neg, neg_zero]
  apply integrable.mono' (integrableOnRpowMulExpNegMulSq hb hs)
  · apply Measurable.aeStronglyMeasurable
    exact
      (measurable_id'.neg.pow measurable_const).mul
        ((measurable_id'.pow measurable_const).const_mul (-b)).exp
  · have : MeasurableSet (Ioi (0 : ℝ)) := measurableSet_ioi
    filter_upwards [ae_restrict_mem this] with x hx
    have h'x : 0 ≤ x := le_of_lt hx
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (exp_pos _).le]
    apply mul_le_mul_of_nonneg_right _ (exp_pos _).le
    simpa [abs_of_nonneg h'x] using abs_rpow_le_abs_rpow (-x) s
#align integrable_rpow_mul_exp_neg_mul_sq integrableRpowMulExpNegMulSq

theorem integrableExpNegMulSq {b : ℝ} (hb : 0 < b) : Integrable fun x : ℝ => exp (-b * x ^ 2) := by
  simpa using integrableRpowMulExpNegMulSq hb (by norm_num : (-1 : ℝ) < 0)
#align integrable_exp_neg_mul_sq integrableExpNegMulSq

theorem integrableOn_ioi_exp_neg_mul_sq_iff {b : ℝ} :
    IntegrableOn (fun x : ℝ => exp (-b * x ^ 2)) (Ioi 0) ↔ 0 < b :=
  by
  refine' ⟨fun h => _, fun h => (integrableExpNegMulSq h).IntegrableOn⟩
  by_contra' hb
  have : (∫⁻ x : ℝ in Ioi 0, 1) ≤ ∫⁻ x : ℝ in Ioi 0, ‖exp (-b * x ^ 2)‖₊ :=
    by
    apply lintegral_mono fun x => _
    simp only [neg_mul, Ennreal.one_le_coe_iff, ← to_nnreal_one, to_nnreal_le_iff_le_coe,
      Real.norm_of_nonneg (exp_pos _).le, coe_nnnorm, one_le_exp_iff, Right.nonneg_neg_iff]
    exact mul_nonpos_of_nonpos_of_nonneg hb (sq_nonneg _)
  simpa using this.trans_lt h.2
#align integrable_on_Ioi_exp_neg_mul_sq_iff integrableOn_ioi_exp_neg_mul_sq_iff

theorem integrable_exp_neg_mul_sq_iff {b : ℝ} :
    (Integrable fun x : ℝ => exp (-b * x ^ 2)) ↔ 0 < b :=
  ⟨fun h => integrableOn_ioi_exp_neg_mul_sq_iff.mp h.IntegrableOn, integrableExpNegMulSq⟩
#align integrable_exp_neg_mul_sq_iff integrable_exp_neg_mul_sq_iff

theorem integrableMulExpNegMulSq {b : ℝ} (hb : 0 < b) :
    Integrable fun x : ℝ => x * exp (-b * x ^ 2) := by
  simpa using integrableRpowMulExpNegMulSq hb (by norm_num : (-1 : ℝ) < 1)
#align integrable_mul_exp_neg_mul_sq integrableMulExpNegMulSq

theorem norm_cexp_neg_mul_sq (b : ℂ) (x : ℝ) : ‖Complex.exp (-b * x ^ 2)‖ = exp (-b.re * x ^ 2) :=
  by
  rw [Complex.norm_eq_abs, Complex.abs_exp, ← of_real_pow, mul_comm (-b) _, of_real_mul_re, neg_re,
    mul_comm]
#align norm_cexp_neg_mul_sq norm_cexp_neg_mul_sq

theorem integrableCexpNegMulSq {b : ℂ} (hb : 0 < b.re) :
    Integrable fun x : ℝ => cexp (-b * x ^ 2) :=
  by
  refine'
    ⟨(complex.continuous_exp.comp
          (continuous_const.mul (continuous_of_real.pow 2))).AeStronglyMeasurable,
      _⟩
  rw [← has_finite_integral_norm_iff]
  simp_rw [norm_cexp_neg_mul_sq]
  exact (integrableExpNegMulSq hb).2
#align integrable_cexp_neg_mul_sq integrableCexpNegMulSq

theorem integrableMulCexpNegMulSq {b : ℂ} (hb : 0 < b.re) :
    Integrable fun x : ℝ => ↑x * cexp (-b * x ^ 2) :=
  by
  refine' ⟨(continuous_of_real.mul (complex.continuous_exp.comp _)).AeStronglyMeasurable, _⟩
  · exact continuous_const.mul (continuous_of_real.pow 2)
  have := (integrableMulExpNegMulSq hb).HasFiniteIntegral
  rw [← has_finite_integral_norm_iff] at this⊢
  convert this
  ext1 x
  rw [norm_mul, norm_mul, norm_cexp_neg_mul_sq b, Complex.norm_eq_abs, abs_of_real,
    Real.norm_eq_abs, norm_of_nonneg (exp_pos _).le]
#align integrable_mul_cexp_neg_mul_sq integrableMulCexpNegMulSq

theorem integral_mul_cexp_neg_mul_sq {b : ℂ} (hb : 0 < b.re) :
    (∫ r : ℝ in Ioi 0, (r : ℂ) * cexp (-b * r ^ 2)) = (2 * b)⁻¹ :=
  by
  have hb' : b ≠ 0 := by
    contrapose! hb
    rw [hb, zero_re]
  refine'
    tendsto_nhds_unique
      (interval_integral_tendsto_integral_Ioi _ (integrableMulCexpNegMulSq hb).IntegrableOn
        Filter.tendsto_id)
      _
  have A :
    ∀ x : ℂ, HasDerivAt (fun x => -(2 * b)⁻¹ * cexp (-b * x ^ 2)) (x * cexp (-b * x ^ 2)) x :=
    by
    intro x
    convert ((hasDerivAt_pow 2 x).const_mul (-b)).cexp.const_mul (-(2 * b)⁻¹) using 1
    field_simp [hb']
    ring
  have :
    ∀ y : ℝ,
      (∫ x in 0 ..id y, ↑x * cexp (-b * x ^ 2)) =
        -(2 * b)⁻¹ * cexp (-b * y ^ 2) - -(2 * b)⁻¹ * cexp (-b * 0 ^ 2) :=
    fun y =>
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x hx => (A x).comp_of_real)
      (integrableMulCexpNegMulSq hb).IntervalIntegrable
  simp_rw [this]
  have L :
    tendsto (fun x : ℝ => (2 * b)⁻¹ - (2 * b)⁻¹ * cexp (-b * x ^ 2)) at_top
      (𝓝 ((2 * b)⁻¹ - (2 * b)⁻¹ * 0)) :=
    by
    refine' tendsto_const_nhds.sub (tendsto.const_mul _ <| tendsto_zero_iff_norm_tendsto_zero.mpr _)
    simp_rw [norm_cexp_neg_mul_sq b]
    exact
      tendsto_exp_at_bot.comp
        (tendsto.neg_const_mul_at_top (neg_lt_zero.2 hb) (tendsto_pow_at_top two_neZero))
  simpa using L
#align integral_mul_cexp_neg_mul_sq integral_mul_cexp_neg_mul_sq

/-- The *square* of the Gaussian integral `∫ x:ℝ, exp (-b * x^2)` is equal to `π / b`. -/
theorem integral_gaussian_sq_complex {b : ℂ} (hb : 0 < b.re) :
    (∫ x : ℝ, cexp (-b * x ^ 2)) ^ 2 = π / b :=
  by/- We compute `(∫ exp (-b x^2))^2` as an integral over `ℝ^2`, and then make a polar change
    of coordinates. We are left with `∫ r * exp (-b r^2)`, which has been computed in
    `integral_mul_cexp_neg_mul_sq` using the fact that this function has an obvious primitive. -/
  calc
    (∫ x : ℝ, cexp (-b * (x : ℂ) ^ 2)) ^ 2 =
        ∫ p : ℝ × ℝ, cexp (-b * (p.1 : ℂ) ^ 2) * cexp (-b * (p.2 : ℂ) ^ 2) :=
      by
      rw [pow_two, ← integral_prod_mul]
      rfl
    _ = ∫ p : ℝ × ℝ, cexp (-b * (p.1 ^ 2 + p.2 ^ 2)) :=
      by
      congr
      ext1 p
      rw [← Complex.exp_add, mul_add]
    _ = ∫ p in polar_coord.target, p.1 • cexp (-b * ((p.1 * cos p.2) ^ 2 + (p.1 * sin p.2) ^ 2)) :=
      by
      rw [← integral_comp_polarCoord_symm]
      simp only [polarCoord_symm_apply, of_real_mul, of_real_cos, of_real_sin]
    _ = (∫ r in Ioi (0 : ℝ), r * cexp (-b * r ^ 2)) * ∫ θ in Ioo (-π) π, 1 :=
      by
      rw [← set_integral_prod_mul]
      congr with p : 1
      rw [mul_one]
      congr
      conv_rhs => rw [← one_mul ((p.1 : ℂ) ^ 2), ← sin_sq_add_cos_sq (p.2 : ℂ)]
      ring
    _ = ↑π / b := by
      have : 0 ≤ π + π := by linarith [Real.pi_pos]
      simp only [integral_const, measure.restrict_apply', measurableSet_ioo, univ_inter, volume_Ioo,
        sub_neg_eq_add, Ennreal.toReal_ofReal, this]
      rw [← two_mul, real_smul, mul_one, of_real_mul, of_real_bit0, of_real_one,
        integral_mul_cexp_neg_mul_sq hb]
      field_simp [(by
          contrapose! hb
          rw [hb, zero_re] : b ≠ 0)]
      ring
    
#align integral_gaussian_sq_complex integral_gaussian_sq_complex

theorem integral_gaussian (b : ℝ) : (∫ x, exp (-b * x ^ 2)) = sqrt (π / b) :=
  by
  -- First we deal with the crazy case where `b ≤ 0`: then both sides vanish.
  rcases le_or_lt b 0 with (hb | hb)
  · rw [integral_undef, sqrt_eq_zero_of_nonpos]
    · exact div_nonpos_of_nonneg_of_nonpos pi_pos.le hb
    · simpa only [not_lt, integrable_exp_neg_mul_sq_iff] using hb
  -- Assume now `b > 0`. Then both sides are non-negative and their squares agree.
  refine' (sq_eq_sq _ (sqrt_nonneg _)).1 _
  · exact integral_nonneg fun x => (exp_pos _).le
  rw [← of_real_inj, of_real_pow, ← integral_of_real, sq_sqrt (div_pos pi_pos hb).le, of_real_div]
  convert integral_gaussian_sq_complex (by rwa [of_real_re] : 0 < (b : ℂ).re)
  ext1 x
  rw [of_real_exp, of_real_mul, of_real_pow, of_real_neg]
#align integral_gaussian integral_gaussian

theorem continuousAt_gaussian_integral (b : ℂ) (hb : 0 < re b) :
    ContinuousAt (fun c : ℂ => ∫ x : ℝ, cexp (-c * x ^ 2)) b :=
  by
  let f : ℂ → ℝ → ℂ := fun (c : ℂ) (x : ℝ) => cexp (-c * x ^ 2)
  obtain ⟨d, hd, hd'⟩ := exists_between hb
  have f_meas : ∀ c : ℂ, ae_strongly_measurable (f c) volume := fun c =>
    by
    apply Continuous.aeStronglyMeasurable
    exact complex.continuous_exp.comp (continuous_const.mul (continuous_of_real.pow 2))
  have f_int : integrable (f b) volume :=
    by
    simp_rw [← integrable_norm_iff (f_meas b), norm_cexp_neg_mul_sq b]
    exact integrableExpNegMulSq hb
  have f_cts : ∀ x : ℝ, ContinuousAt (fun c => f c x) b := fun x =>
    (complex.continuous_exp.comp (continuous_id'.neg.mul continuous_const)).ContinuousAt
  have f_le_bd : ∀ᶠ c : ℂ in 𝓝 b, ∀ᵐ x : ℝ, ‖f c x‖ ≤ exp (-d * x ^ 2) :=
    by
    refine' eventually_of_mem ((continuous_re.is_open_preimage _ isOpen_ioi).mem_nhds hd') _
    refine' fun c hc => ae_of_all _ fun x => _
    rw [norm_cexp_neg_mul_sq, exp_le_exp]
    exact mul_le_mul_of_nonneg_right (neg_le_neg (le_of_lt hc)) (sq_nonneg _)
  exact
    continuous_at_of_dominated (eventually_of_forall f_meas) f_le_bd (integrableExpNegMulSq hd)
      (ae_of_all _ f_cts)
#align continuous_at_gaussian_integral continuousAt_gaussian_integral

theorem integral_gaussian_complex {b : ℂ} (hb : 0 < re b) :
    (∫ x : ℝ, cexp (-b * x ^ 2)) = (π / b) ^ (1 / 2 : ℂ) :=
  by
  have nv : ∀ {b : ℂ}, 0 < re b → b ≠ 0 := by
    intro b hb
    contrapose! hb
    rw [hb]
    simp
  refine'
    (convex_halfspace_re_gt 0).IsPreconnected.eq_of_sq_eq _ _ (fun c hc => _) (fun c hc => _)
      (by simp : 0 < re (1 : ℂ)) _ hb
  ·-- integral is continuous
    exact ContinuousAt.continuousOn continuousAt_gaussian_integral
  · -- `(π / b) ^ (1 / 2 : ℂ)` is continuous
    refine'
      ContinuousAt.continuousOn fun b hb =>
        (continuousAt_cpow_const (Or.inl _)).comp (continuous_at_const.div continuousAt_id (nv hb))
    rw [div_re, of_real_im, of_real_re, zero_mul, zero_div, add_zero]
    exact div_pos (mul_pos pi_pos hb) (norm_sq_pos.mpr (nv hb))
  · -- squares of both sides agree
    dsimp only [Pi.pow_apply]
    rw [integral_gaussian_sq_complex hc, sq]
    conv_lhs => rw [← cpow_one (↑π / c)]
    rw [← cpow_add _ _ (div_ne_zero (of_real_ne_zero.mpr pi_ne_zero) (nv hc))]
    norm_num
  · -- RHS doesn't vanish
    rw [Ne.def, cpow_eq_zero_iff, not_and_or]
    exact Or.inl (div_ne_zero (of_real_ne_zero.mpr pi_ne_zero) (nv hc))
  · -- equality at 1
    have : ∀ x : ℝ, cexp (-1 * x ^ 2) = exp (-1 * x ^ 2) :=
      by
      intro x
      simp only [of_real_exp, neg_mul, one_mul, of_real_neg, of_real_pow]
    simp_rw [this, integral_of_real]
    conv_rhs =>
      congr
      rw [← of_real_one, ← of_real_div]
      skip
      rw [← of_real_one, ← of_real_bit0, ← of_real_div]
    rw [← of_real_cpow, of_real_inj]
    convert integral_gaussian (1 : ℝ)
    · rwa [sqrt_eq_rpow]
    · rw [div_one]
      exact pi_pos.le
#align integral_gaussian_complex integral_gaussian_complex

-- The Gaussian integral on the half-line, `∫ x in Ioi 0, exp (-b * x^2)`, for complex `b`.
theorem integral_gaussian_complex_ioi {b : ℂ} (hb : 0 < re b) :
    (∫ x : ℝ in Ioi 0, cexp (-b * x ^ 2)) = (π / b) ^ (1 / 2 : ℂ) / 2 :=
  by
  have full_integral := integral_gaussian_complex hb
  have : MeasurableSet (Ioi (0 : ℝ)) := measurableSet_ioi
  rw [← integral_add_compl this (integrableCexpNegMulSq hb), compl_Ioi] at full_integral
  suffices (∫ x : ℝ in Iic 0, cexp (-b * x ^ 2)) = ∫ x : ℝ in Ioi 0, cexp (-b * x ^ 2)
    by
    rw [this, ← mul_two] at full_integral
    rwa [eq_div_iff]
    exact two_neZero
  have : ∀ c : ℝ, (∫ x in 0 ..c, cexp (-b * x ^ 2)) = ∫ x in -c..0, cexp (-b * x ^ 2) :=
    by
    intro c
    have := @intervalIntegral.integral_comp_sub_left _ _ _ _ 0 c (fun x => cexp (-b * x ^ 2)) 0
    simpa [zero_sub, neg_sq, neg_zero] using this
  have t1 :=
    interval_integral_tendsto_integral_Ioi _ (integrableCexpNegMulSq hb).IntegrableOn tendsto_id
  have t2 :
    tendsto (fun c : ℝ => ∫ x : ℝ in 0 ..c, cexp (-b * x ^ 2)) at_top
      (𝓝 (∫ x : ℝ in Iic 0, cexp (-b * x ^ 2))) :=
    by
    simp_rw [this]
    refine' interval_integral_tendsto_integral_Iic _ _ tendsto_neg_at_top_at_bot
    apply (integrableCexpNegMulSq hb).IntegrableOn
  exact tendsto_nhds_unique t2 t1
#align integral_gaussian_complex_Ioi integral_gaussian_complex_ioi

-- The Gaussian integral on the half-line, `∫ x in Ioi 0, exp (-b * x^2)`, for real `b`.
theorem integral_gaussian_ioi (b : ℝ) : (∫ x in Ioi 0, exp (-b * x ^ 2)) = sqrt (π / b) / 2 :=
  by
  rcases le_or_lt b 0 with (hb | hb)
  · rw [integral_undef, sqrt_eq_zero_of_nonpos, zero_div]
    exact div_nonpos_of_nonneg_of_nonpos pi_pos.le hb
    rwa [← integrable_on, integrableOn_ioi_exp_neg_mul_sq_iff, not_lt]
  rw [← of_real_inj, ← integral_of_real]
  convert integral_gaussian_complex_ioi (by rwa [of_real_re] : 0 < (b : ℂ).re)
  · ext1 x
    simp
  · rw [sqrt_eq_rpow, ← of_real_div, of_real_div, of_real_cpow]
    norm_num
    exact (div_pos pi_pos hb).le
#align integral_gaussian_Ioi integral_gaussian_ioi

namespace Complex

/-- The special-value formula `Γ(1/2) = √π`, which is equivalent to the Gaussian integral. -/
theorem gamma_one_half_eq : gamma (1 / 2) = sqrt π :=
  by
  -- first reduce to real integrals
  have hh : (1 / 2 : ℂ) = ↑(1 / 2 : ℝ) := by
    simp only [one_div, of_real_inv, of_real_bit0, of_real_one]
  have hh2 : (1 / 2 : ℂ).re = 1 / 2 := by convert of_real_re (1 / 2 : ℝ)
  replace hh2 : 0 < (1 / 2 : ℂ).re := by
    rw [hh2]
    exact one_half_pos
  rw [Gamma_eq_integral hh2, hh, Gamma_integral_of_real, of_real_inj]
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
    have : (x ^ (2 : ℝ)) ^ (1 / (2 : ℝ) - 1) = x⁻¹ :=
      by
      rw [← rpow_mul (le_of_lt hx)]
      norm_num
      rw [rpow_neg (le_of_lt hx), rpow_one]
    rw [smul_eq_mul, this]
    field_simp [(ne_of_lt hx).symm]
    norm_num
    ring
  rw [set_integral_congr measurableSet_ioi this, integral_mul_left, integral_gaussian_ioi]
  field_simp
  ring
#align complex.Gamma_one_half_eq Complex.gamma_one_half_eq

end Complex

