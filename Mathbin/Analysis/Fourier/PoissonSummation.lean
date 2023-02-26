/-
Copyright (c) 2023 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler

! This file was ported from Lean 3 source module analysis.fourier.poisson_summation
! leanprover-community/mathlib commit 3353f3371120058977ce1e20bf7fc8986c0fb042
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Analysis.Fourier.AddCircle
import Mathbin.Analysis.Fourier.FourierTransform

/-!
# Poisson's summation formula

We prove Poisson's summation formula `∑ (n : ℤ), f n = ∑ (n : ℤ), 𝓕 f n`, where `𝓕 f` is the
Fourier transform of `f`, under the following hypotheses:
* `f` is a continuous function `ℝ → ℂ`.
* The sum `∑ (n : ℤ), 𝓕 f n` is convergent.
* For all compacts `K ⊂ ℝ`, the sum `∑ (n : ℤ), sup { ‖f(x + n)‖ | x ∈ K }` is convergent.

## TODO

* Show that the conditions on `f` are automatically satisfied for Schwartz functions.
-/


noncomputable section

open Function hiding comp_apply

open Complex Real

open Set hiding restrict_apply

open TopologicalSpace Filter MeasureTheory

open Real BigOperators Filter FourierTransform

attribute [local instance] Real.fact_zero_lt_one

open ContinuousMap

/-- The key lemma for Poisson summation: the `m`-th Fourier coefficient of the periodic function
`∑' n : ℤ, f (x + n)` is the value at `m` of the Fourier transform of `f`. -/
theorem Real.fourierCoeff_tsum_comp_add {f : C(ℝ, ℂ)}
    (hf : ∀ K : Compacts ℝ, Summable fun n : ℤ => ‖(f.comp (ContinuousMap.addRight n)).restrict K‖)
    (m : ℤ) : fourierCoeff (Periodic.lift <| f.periodic_tsum_comp_add_zsmul 1) m = 𝓕 f m :=
  by
  -- NB: This proof can be shortened somewhat by telescoping together some of the steps in the calc
  -- block, but I think it's more legible this way. We start with preliminaries about the integrand.
  let e : C(ℝ, ℂ) := (fourier (-m)).comp ⟨(coe : ℝ → UnitAddCircle), continuous_quotient_mk'⟩
  have neK : ∀ (K : compacts ℝ) (g : C(ℝ, ℂ)), ‖(e * g).restrict K‖ = ‖g.restrict K‖ :=
    by
    have : ∀ x : ℝ, ‖e x‖ = 1 := fun x => abs_coe_circle _
    intro K g
    simp_rw [norm_eq_supr_norm, restrict_apply, mul_apply, norm_mul, this, one_mul]
  have eadd : ∀ n : ℤ, e.comp (ContinuousMap.addRight n) = e :=
    by
    intro n
    ext1 x
    have : periodic e 1 := periodic.comp (fun x => AddCircle.coe_add_period 1 x) _
    simpa only [mul_one] using this.int_mul n x
  -- Now the main argument. First unwind some definitions.
  calc
    fourierCoeff (periodic.lift <| f.periodic_tsum_comp_add_zsmul 1) m =
        ∫ x in 0 ..1, e x * (∑' n : ℤ, f.comp (ContinuousMap.addRight n)) x :=
      by
      simp_rw [fourierCoeff_eq_intervalIntegral _ m 0, div_one, one_smul, zero_add, comp_apply,
        coe_mk, periodic.lift_coe, zsmul_one, smul_eq_mul]
    -- Transform sum in C(ℝ, ℂ) evaluated at x into pointwise sum of values.
        _ =
        ∫ x in 0 ..1, ∑' n : ℤ, (e * f.comp (ContinuousMap.addRight n)) x :=
      by
      simp_rw [coe_mul, Pi.mul_apply, ← tsum_apply (summable_of_locally_summable_norm hf),
        tsum_mul_left]
    -- Swap sum and integral.
        _ =
        ∑' n : ℤ, ∫ x in 0 ..1, (e * f.comp (ContinuousMap.addRight n)) x :=
      by
      refine' (intervalIntegral.tsum_intervalIntegral_eq_of_summable_norm _).symm
      convert hf ⟨uIcc 0 1, isCompact_uIcc⟩
      exact funext fun n => neK _ _
    _ = ∑' n : ℤ, ∫ x in 0 ..1, (e * f).comp (ContinuousMap.addRight n) x :=
      by
      simp only [ContinuousMap.comp_apply, mul_comp] at eadd⊢
      simp_rw [eadd]
    -- Rearrange sum of interval integrals into an integral over `ℝ`.
        _ =
        ∫ x, e x * f x :=
      by
      suffices : integrable ⇑(e * f); exact this.has_sum_interval_integral_comp_add_int.tsum_eq
      apply integrable_of_summable_norm_Icc
      convert hf ⟨Icc 0 1, is_compact_Icc⟩
      simp_rw [ContinuousMap.comp_apply, mul_comp] at eadd⊢
      simp_rw [eadd]
      exact funext fun n => neK ⟨Icc 0 1, is_compact_Icc⟩ _
    -- Minor tidying to finish
        _ =
        𝓕 f m :=
      by
      rw [fourier_integral_eq_integral_exp_smul]
      congr 1 with x : 1
      rw [smul_eq_mul, comp_apply, coe_mk, fourier_coe_apply]
      congr 2
      push_cast
      ring
    
#align real.fourier_coeff_tsum_comp_add Real.fourierCoeff_tsum_comp_add

/-- **Poisson's summation formula**. -/
theorem Real.tsum_eq_tsum_fourierIntegral {f : C(ℝ, ℂ)}
    (h_norm :
      ∀ K : Compacts ℝ, Summable fun n : ℤ => ‖(f.comp <| ContinuousMap.addRight n).restrict K‖)
    (h_sum : Summable fun n : ℤ => 𝓕 f n) : (∑' n : ℤ, f n) = ∑' n : ℤ, 𝓕 f n :=
  by
  let F : C(UnitAddCircle, ℂ) :=
    ⟨(f.periodic_tsum_comp_add_zsmul 1).lift, continuous_coinduced_dom.mpr (map_continuous _)⟩
  have : Summable (fourierCoeff F) := by
    convert h_sum
    exact funext fun n => Real.fourierCoeff_tsum_comp_add h_norm n
  convert (has_pointwise_sum_fourier_series_of_summable this 0).tsum_eq.symm using 1
  · have := (has_sum_apply (summable_of_locally_summable_norm h_norm).HasSum 0).tsum_eq
    simpa only [coe_mk, ← QuotientAddGroup.mk_zero, periodic.lift_coe, zsmul_one, comp_apply,
      coe_add_right, zero_add] using this
  · congr 1 with n : 1
    rw [← Real.fourierCoeff_tsum_comp_add h_norm n, fourier_eval_zero, smul_eq_mul, mul_one]
    rfl
#align real.tsum_eq_tsum_fourier_integral Real.tsum_eq_tsum_fourierIntegral

