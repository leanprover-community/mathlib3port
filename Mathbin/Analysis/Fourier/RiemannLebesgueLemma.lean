/-
Copyright (c) 2022 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler

! This file was ported from Lean 3 source module analysis.fourier.riemann_lebesgue_lemma
! leanprover-community/mathlib commit 28aa996fc6fb4317f0083c4e6daf79878d81be33
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.MeasureTheory.Function.ContinuousMapDense
import Mathbin.MeasureTheory.Integral.IntegralEqImproper
import Mathbin.MeasureTheory.Group.Integration
import Mathbin.Topology.ContinuousFunction.ZeroAtInfty
import Mathbin.Analysis.Fourier.FourierTransform

/-!
# The Riemann-Lebesgue Lemma

In this file we prove a weak form of the Riemann-Lebesgue lemma, stating that for any
compactly-supported continuous function `f` on `ℝ` (valued in some complete normed space `E`), the
integral

`∫ (x : ℝ), exp (↑(t * x) * I) • f x`

tends to zero as `t → ∞`. (The actual lemma is that this holds for all `L¹` functions `f`, which
follows from the result proved here together with the fact that continuous, compactly-supported
functions are dense in `L¹(ℝ)`, which will be proved in a future iteration.)

## Main results

- `tendsto_integral_mul_exp_at_top_of_continuous_compact_support`: the Riemann-Lebesgue lemma for
  continuous compactly-supported functions on `ℝ`.
-/


open MeasureTheory Filter Complex Set

open Filter Topology Real Ennreal

section ContinuousCompactSupport

variable {E : Type _} [NormedAddCommGroup E] [NormedSpace ℂ E] {f : ℝ → E}

/-- The integrand in the Riemann-Lebesgue lemma is integrable. -/
theorem fourierIntegrandIntegrable (hf : Integrable f) (t : ℝ) :
    Integrable fun x : ℝ => exp (↑(t * x) * i) • f x :=
  by
  rw [← integrable_norm_iff]
  simp_rw [norm_smul, norm_exp_of_real_mul_I, one_mul]
  exacts[hf.norm, (Continuous.aeStronglyMeasurable (by continuity)).smul hf.1]
#align fourier_integrand_integrable fourierIntegrandIntegrable

variable [CompleteSpace E]

/-- Shifting `f` by `π / t` negates the integral in the Riemann-Lebesgue lemma. -/
theorem fourier_integral_half_period_translate {t : ℝ} (ht : t ≠ 0) :
    (∫ x : ℝ, exp (↑(t * x) * i) • f (x + π / t)) = -∫ x : ℝ, exp (↑(t * x) * i) • f x :=
  by
  have :
    (fun x : ℝ => exp (↑(t * x) * I) • f (x + π / t)) = fun x : ℝ =>
      (fun y : ℝ => -exp (↑(t * y) * I) • f y) (x + π / t) :=
    by
    ext1 x
    dsimp only
    rw [of_real_mul, of_real_mul, of_real_add, mul_add, add_mul, exp_add, ← neg_mul]
    replace ht := complex.of_real_ne_zero.mpr ht
    have : ↑t * ↑(π / t) * I = π * I := by
      field_simp
      ring
    rw [this, exp_pi_mul_I]
    ring_nf
  rw [this, integral_add_right_eq_self]
  simp_rw [neg_smul, integral_neg]
#align fourier_integral_half_period_translate fourier_integral_half_period_translate

/-- Rewrite the Riemann-Lebesgue integral in a form that allows us to use uniform continuity. -/
theorem fourier_integral_eq_half_sub_half_period_translate {t : ℝ} (ht : t ≠ 0)
    (hf : Integrable f) :
    (∫ x : ℝ, exp (↑(t * x) * i) • f x) =
      (1 / (2 : ℂ)) • ∫ x : ℝ, exp (↑(t * x) * i) • (f x - f (x + π / t)) :=
  by
  simp_rw [smul_sub]
  rw [integral_sub, fourier_integral_half_period_translate ht, sub_eq_add_neg, neg_neg, ←
    two_smul ℂ _, ← @smul_assoc _ _ _ _ _ _ (IsScalarTower.left ℂ), smul_eq_mul]
  norm_num
  exacts[fourierIntegrandIntegrable hf t, fourierIntegrandIntegrable (hf.comp_add_right (π / t)) t]
#align fourier_integral_eq_half_sub_half_period_translate fourier_integral_eq_half_sub_half_period_translate

/-- Riemann-Lebesgue Lemma for continuous and compactly-supported functions: the integral
`∫ x, exp (t * x * I) • f x` tends to 0 as `t` gets large.  -/
theorem tendsto_integral_mul_exp_atTop_of_continuous_compact_support (hf1 : Continuous f)
    (hf2 : HasCompactSupport f) :
    Tendsto (fun t : ℝ => ∫ x : ℝ, exp (↑(t * x) * i) • f x) atTop (𝓝 0) :=
  by
  simp_rw [NormedAddCommGroup.tendsto_nhds_zero, eventually_at_top, ge_iff_le]
  intro ε hε
  -- Extract an explicit candidate bound on `t` from uniform continuity.
  obtain ⟨R, hR1, hR2⟩ := hf2.exists_pos_le_norm
  obtain ⟨δ, hδ1, hδ2⟩ :=
    metric.uniform_continuous_iff.mp (hf2.uniform_continuous_of_continuous hf1) (ε / (1 + 2 * R))
      (div_pos hε (by positivity))
  refine' ⟨max π (1 + π / δ), fun t ht => _⟩
  have tpos : 0 < t := lt_of_lt_of_le Real.pi_pos ((le_max_left _ _).trans ht)
  -- Rewrite integral in terms of `f x - f (x + π / t)`.
  rw [fourier_integral_eq_half_sub_half_period_translate
      (lt_of_lt_of_le (lt_max_of_lt_left Real.pi_pos) ht).ne'
      (hf1.integrable_of_has_compact_support hf2)]
  rw [norm_smul, norm_eq_abs, ← Complex.of_real_one, ← of_real_bit0, ← of_real_div,
    Complex.abs_of_nonneg one_half_pos.le]
  have : ε = 1 / 2 * (2 * ε) := by
    field_simp
    ring
  rw [this, mul_lt_mul_left (one_half_pos : (0 : ℝ) < 1 / 2)]
  have :
    ‖∫ x : ℝ, exp (↑(t * x) * I) • (f x - f (x + π / t))‖ ≤
      ∫ x : ℝ, ‖exp (↑(t * x) * I) • (f x - f (x + π / t))‖ :=
    norm_integral_le_integral_norm _
  refine' lt_of_le_of_lt this _
  simp_rw [norm_smul, norm_exp_of_real_mul_I, one_mul]
  -- Show integral can be taken over `[-(R + 1), R] ⊂ ℝ`.
  let A := Icc (-(R + 1)) R
  have int_Icc : (∫ x : ℝ, ‖f x - f (x + π / t)‖) = ∫ x in A, ‖f x - f (x + π / t)‖ :=
    by
    refine' (set_integral_eq_integral_of_forall_compl_eq_zero fun x hx => _).symm
    rw [mem_Icc, not_and_or, not_le, not_le, lt_neg] at hx
    suffices f x = 0 ∧ f (x + π / t) = 0 by rw [this.1, this.2, sub_zero, norm_zero]
    have tp : 0 < t := real.pi_pos.trans_le ((le_max_left _ _).trans ht)
    refine' ⟨hR2 x <| le_abs.mpr _, hR2 _ <| le_abs.mpr _⟩
    · cases hx
      · exact Or.inr ((le_add_of_nonneg_right zero_le_one).trans hx.le)
      · exact Or.inl hx.le
    · cases hx
      · refine' Or.inr _
        rw [neg_add, ← sub_eq_add_neg, le_sub_iff_add_le]
        refine' le_trans (add_le_add_left _ R) hx.le
        exact (div_le_one tp).mpr ((le_max_left _ _).trans ht)
      · exact Or.inl (hx.trans <| lt_add_of_pos_right _ <| div_pos Real.pi_pos tp).le
  rw [int_Icc]
  -- Bound integral using fact that ‖f x - f (x + π / t)‖ is small.
  have bdA : ∀ x : ℝ, x ∈ A → ‖‖f x - f (x + π / t)‖‖ ≤ ε / (1 + 2 * R) :=
    by
    simp_rw [norm_norm]
    refine' fun x _ => le_of_lt _
    simp_rw [dist_eq_norm] at hδ2
    apply hδ2
    rw [sub_add_cancel', Real.norm_eq_abs, abs_neg, abs_of_pos (div_pos Real.pi_pos tpos),
      div_lt_iff tpos, mul_comm, ← div_lt_iff hδ1]
    linarith [(le_max_right π (1 + π / δ)).trans ht]
  have bdA2 := norm_set_integral_le_of_norm_le_const (measure_Icc_lt_top : volume A < ∞) bdA _
  swap
  · apply Continuous.aeStronglyMeasurable
    exact
      continuous_norm.comp <|
        Continuous.sub hf1 <| Continuous.comp hf1 <| continuous_id'.add continuous_const
  have : ‖_‖ = ∫ x : ℝ in A, ‖f x - f (x + π / t)‖ :=
    Real.norm_of_nonneg (set_integral_nonneg measurableSet_Icc fun x hx => norm_nonneg _)
  rw [this] at bdA2
  refine' lt_of_le_of_lt bdA2 _
  rw [Real.volume_Icc, (by ring : R - -(R + 1) = 1 + 2 * R)]
  have hh : 0 < 1 + 2 * R := by positivity
  rw [Ennreal.toReal_ofReal hh.le, div_mul_cancel _ hh.ne', two_mul]
  exact lt_add_of_pos_left _ hε
#align tendsto_integral_mul_exp_at_top_of_continuous_compact_support tendsto_integral_mul_exp_atTop_of_continuous_compact_support

theorem tendsto_integral_mul_exp_atBot_of_continuous_compact_support (hf1 : Continuous f)
    (hf2 : HasCompactSupport f) :
    Tendsto (fun t : ℝ => ∫ x : ℝ, exp (↑(t * x) * i) • f x) atBot (𝓝 0) :=
  by
  have hg2 : HasCompactSupport (f ∘ Neg.neg) := by
    simpa only [neg_one_smul] using hf2.comp_smul (neg_ne_zero.mpr <| one_ne_zero' ℝ)
  convert
    (tendsto_integral_mul_exp_atTop_of_continuous_compact_support (hf1.comp continuous_neg)
          hg2).comp
      tendsto_neg_at_bot_at_top
  ext1 t
  simp_rw [Function.comp_apply, neg_mul, ← mul_neg]
  rw [← integral_neg_eq_self]
#align tendsto_integral_mul_exp_at_bot_of_continuous_compact_support tendsto_integral_mul_exp_atBot_of_continuous_compact_support

theorem zero_at_infty_integral_mul_exp_of_continuous_compact_support (hf1 : Continuous f)
    (hf2 : HasCompactSupport f) :
    Tendsto (fun t : ℝ => ∫ x : ℝ, exp (↑(t * x) * i) • f x) (cocompact ℝ) (𝓝 0) :=
  by
  rw [Real.cocompact_eq, tendsto_sup]
  exact
    ⟨tendsto_integral_mul_exp_atBot_of_continuous_compact_support hf1 hf2,
      tendsto_integral_mul_exp_atTop_of_continuous_compact_support hf1 hf2⟩
#align zero_at_infty_integral_mul_exp_of_continuous_compact_support zero_at_infty_integral_mul_exp_of_continuous_compact_support

open FourierTransform

/-- Riemann-Lebesgue lemma for continuous compactly-supported functions: the Fourier transform
tends to 0 at infinity. -/
theorem Real.fourierIntegral_zero_at_infty_of_continuous_compact_support (hc : Continuous f)
    (hs : HasCompactSupport f) : Tendsto (Real.fourierIntegral f) (cocompact ℝ) (𝓝 0) :=
  by
  refine'
    ((zero_at_infty_integral_mul_exp_of_continuous_compact_support hc hs).comp
          (tendsto_cocompact_mul_left₀
            (mul_ne_zero (neg_ne_zero.mpr two_ne_zero) real.pi_pos.ne'))).congr
      fun w => _
  rw [Real.fourierIntegral_eq_integral_exp_smul, Function.comp_apply]
  congr 1 with x : 1
  ring_nf
#align real.fourier_integral_zero_at_infty_of_continuous_compact_support Real.fourierIntegral_zero_at_infty_of_continuous_compact_support

end ContinuousCompactSupport

