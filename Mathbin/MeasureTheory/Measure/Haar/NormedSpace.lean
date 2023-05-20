/-
Copyright (c) 2020 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Sébastien Gouëzel

! This file was ported from Lean 3 source module measure_theory.measure.haar.normed_space
! leanprover-community/mathlib commit fd5edc43dc4f10b85abfe544b88f82cf13c5f844
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathbin.MeasureTheory.Integral.Bochner

/-!
# Basic properties of Haar measures on real vector spaces

-/


noncomputable section

open NNReal ENNReal Pointwise BigOperators Topology

open Inv Set Function MeasureTheory.Measure Filter

open Measure FiniteDimensional

namespace MeasureTheory

namespace Measure

/- The instance `is_add_haar_measure.has_no_atoms` applies in particular to show that an additive
Haar measure on a nontrivial finite-dimensional real vector space has no atom. -/
example {E : Type _} [NormedAddCommGroup E] [NormedSpace ℝ E] [Nontrivial E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [IsAddHaarMeasure μ] : NoAtoms μ := by
  infer_instance

section ContinuousLinearEquiv

variable {𝕜 G H : Type _} [MeasurableSpace G] [MeasurableSpace H] [NontriviallyNormedField 𝕜]
  [TopologicalSpace G] [TopologicalSpace H] [AddCommGroup G] [AddCommGroup H]
  [TopologicalAddGroup G] [TopologicalAddGroup H] [Module 𝕜 G] [Module 𝕜 H] (μ : Measure G)
  [IsAddHaarMeasure μ] [BorelSpace G] [BorelSpace H] [T2Space H]

instance MapContinuousLinearEquiv.isAddHaarMeasure (e : G ≃L[𝕜] H) : IsAddHaarMeasure (μ.map e) :=
  e.toAddEquiv.is_add_haar_measure_map _ e.Continuous e.symm.Continuous
#align measure_theory.measure.map_continuous_linear_equiv.is_add_haar_measure MeasureTheory.Measure.MapContinuousLinearEquiv.isAddHaarMeasure

variable [CompleteSpace 𝕜] [T2Space G] [FiniteDimensional 𝕜 G] [ContinuousSMul 𝕜 G]
  [ContinuousSMul 𝕜 H]

instance MapLinearEquiv.isAddHaarMeasure (e : G ≃ₗ[𝕜] H) : IsAddHaarMeasure (μ.map e) :=
  MapContinuousLinearEquiv.isAddHaarMeasure _ e.toContinuousLinearEquiv
#align measure_theory.measure.map_linear_equiv.is_add_haar_measure MeasureTheory.Measure.MapLinearEquiv.isAddHaarMeasure

end ContinuousLinearEquiv

variable {E : Type _} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
  [FiniteDimensional ℝ E] (μ : Measure E) [IsAddHaarMeasure μ] {F : Type _} [NormedAddCommGroup F]
  [NormedSpace ℝ F] [CompleteSpace F]

variable (μ) {s : Set E}

/-- The integral of `f (R • x)` with respect to an additive Haar measure is a multiple of the
integral of `f`. The formula we give works even when `f` is not integrable or `R = 0`
thanks to the convention that a non-integrable function has integral zero. -/
theorem integral_comp_smul (f : E → F) (R : ℝ) :
    (∫ x, f (R • x) ∂μ) = |(R ^ finrank ℝ E)⁻¹| • ∫ x, f x ∂μ :=
  by
  rcases eq_or_ne R 0 with (rfl | hR)
  · simp only [zero_smul, integral_const]
    rcases Nat.eq_zero_or_pos (finrank ℝ E) with (hE | hE)
    · have : Subsingleton E := finrank_zero_iff.1 hE
      have : f = fun x => f 0 := by
        ext x
        rw [Subsingleton.elim x 0]
      conv_rhs => rw [this]
      simp only [hE, pow_zero, inv_one, abs_one, one_smul, integral_const]
    · have : Nontrivial E := finrank_pos_iff.1 hE
      simp only [zero_pow hE, measure_univ_of_is_add_left_invariant, ENNReal.top_toReal, zero_smul,
        inv_zero, abs_zero]
  ·
    calc
      (∫ x, f (R • x) ∂μ) = ∫ y, f y ∂measure.map (fun x => R • x) μ :=
        (integral_map_equiv (Homeomorph.smul (isUnit_iff_ne_zero.2 hR).Unit).toMeasurableEquiv
            f).symm
      _ = |(R ^ finrank ℝ E)⁻¹| • ∫ x, f x ∂μ := by
        simp only [map_add_haar_smul μ hR, integral_smul_measure, ENNReal.toReal_ofReal, abs_nonneg]
      
#align measure_theory.measure.integral_comp_smul MeasureTheory.Measure.integral_comp_smul

/-- The integral of `f (R • x)` with respect to an additive Haar measure is a multiple of the
integral of `f`. The formula we give works even when `f` is not integrable or `R = 0`
thanks to the convention that a non-integrable function has integral zero. -/
theorem integral_comp_smul_of_nonneg (f : E → F) (R : ℝ) {hR : 0 ≤ R} :
    (∫ x, f (R • x) ∂μ) = (R ^ finrank ℝ E)⁻¹ • ∫ x, f x ∂μ := by
  rw [integral_comp_smul μ f R, abs_of_nonneg (inv_nonneg.2 (pow_nonneg hR _))]
#align measure_theory.measure.integral_comp_smul_of_nonneg MeasureTheory.Measure.integral_comp_smul_of_nonneg

/-- The integral of `f (R⁻¹ • x)` with respect to an additive Haar measure is a multiple of the
integral of `f`. The formula we give works even when `f` is not integrable or `R = 0`
thanks to the convention that a non-integrable function has integral zero. -/
theorem integral_comp_inv_smul (f : E → F) (R : ℝ) :
    (∫ x, f (R⁻¹ • x) ∂μ) = |R ^ finrank ℝ E| • ∫ x, f x ∂μ := by
  rw [integral_comp_smul μ f R⁻¹, inv_pow, inv_inv]
#align measure_theory.measure.integral_comp_inv_smul MeasureTheory.Measure.integral_comp_inv_smul

/-- The integral of `f (R⁻¹ • x)` with respect to an additive Haar measure is a multiple of the
integral of `f`. The formula we give works even when `f` is not integrable or `R = 0`
thanks to the convention that a non-integrable function has integral zero. -/
theorem integral_comp_inv_smul_of_nonneg (f : E → F) {R : ℝ} (hR : 0 ≤ R) :
    (∫ x, f (R⁻¹ • x) ∂μ) = R ^ finrank ℝ E • ∫ x, f x ∂μ := by
  rw [integral_comp_inv_smul μ f R, abs_of_nonneg (pow_nonneg hR _)]
#align measure_theory.measure.integral_comp_inv_smul_of_nonneg MeasureTheory.Measure.integral_comp_inv_smul_of_nonneg

end Measure

end MeasureTheory

