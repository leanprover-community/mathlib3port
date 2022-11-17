/-
Copyright (c) 2022 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
import Mathbin.MeasureTheory.Measure.MeasureSpace
import Mathbin.Analysis.SpecialFunctions.Log.Base

/-!
# Doubling measures

A doubling measure `μ` on a metric space is a measure for which there exists a constant `C` such
that for all sufficiently small radii `ε`, and for any centre, the measure of a ball of radius
`2 * ε` is bounded by `C` times the measure of the concentric ball of radius `ε`.

This file records basic files on doubling measures.

## Main definitions

  * `is_doubling_measure`: the definition of a doubling measure (as a typeclass).
  * `is_doubling_measure.doubling_constant`: a function yielding the doubling constant `C` appearing
  in the definition of a doubling measure.
-/


noncomputable section

open Set Filter Metric MeasureTheory TopologicalSpace

open Nnreal TopologicalSpace

/- ./././Mathport/Syntax/Translate/Command.lean:355:30: infer kinds are unsupported in Lean 4: #[`exists_measure_closed_ball_le_mul] [] -/
/-- A measure `μ` is said to be a doubling measure if there exists a constant `C` such that for
all sufficiently small radii `ε`, and for any centre, the measure of a ball of radius `2 * ε` is
bounded by `C` times the measure of the concentric ball of radius `ε`.

Note: it is important that this definition makes a demand only for sufficiently small `ε`. For
example we want hyperbolic space to carry the instance `is_doubling_measure volume` but volumes grow
exponentially in hyperbolic space. To be really explicit, consider the hyperbolic plane of
curvature -1, the area of a disc of radius `ε` is `A(ε) = 2π(cosh(ε) - 1)` so `A(2ε)/A(ε) ~ exp(ε)`.
-/
class IsDoublingMeasure {α : Type _} [MetricSpace α] [MeasurableSpace α] (μ : Measure α) where
  exists_measure_closed_ball_le_mul : ∃ C : ℝ≥0, ∀ᶠ ε in 𝓝[>] 0, ∀ x, μ (closedBall x (2 * ε)) ≤ C * μ (closedBall x ε)
#align is_doubling_measure IsDoublingMeasure

namespace IsDoublingMeasure

variable {α : Type _} [MetricSpace α] [MeasurableSpace α] (μ : Measure α) [IsDoublingMeasure μ]

/-- A doubling constant for a doubling measure.

See also `is_doubling_measure.scaling_constant_of`. -/
def doublingConstant : ℝ≥0 :=
  Classical.choose $ exists_measure_closed_ball_le_mul μ
#align is_doubling_measure.doubling_constant IsDoublingMeasure.doublingConstant

theorem exists_measure_closed_ball_le_mul' :
    ∀ᶠ ε in 𝓝[>] 0, ∀ x, μ (closedBall x (2 * ε)) ≤ doublingConstant μ * μ (closedBall x ε) :=
  Classical.choose_spec $ exists_measure_closed_ball_le_mul μ
#align is_doubling_measure.exists_measure_closed_ball_le_mul' IsDoublingMeasure.exists_measure_closed_ball_le_mul'

theorem exists_eventually_forall_measure_closed_ball_le_mul (K : ℝ) :
    ∃ C : ℝ≥0, ∀ᶠ ε in 𝓝[>] 0, ∀ (x t) (ht : t ≤ K), μ (closedBall x (t * ε)) ≤ C * μ (closedBall x ε) := by
  let C := doubling_constant μ
  have hμ : ∀ n : ℕ, ∀ᶠ ε in 𝓝[>] 0, ∀ x, μ (closed_ball x (2 ^ n * ε)) ≤ ↑(C ^ n) * μ (closed_ball x ε) := by
    intro n
    induction' n with n ih
    · simp
      
    replace ih := eventually_nhds_within_pos_mul_left (two_pos : 0 < (2 : ℝ)) ih
    refine' (ih.and (exists_measure_closed_ball_le_mul' μ)).mono fun ε hε x => _
    calc
      μ (closed_ball x (2 ^ (n + 1) * ε)) = μ (closed_ball x (2 ^ n * (2 * ε))) := by rw [pow_succ', mul_assoc]
      _ ≤ ↑(C ^ n) * μ (closed_ball x (2 * ε)) := hε.1 x
      _ ≤ ↑(C ^ n) * (C * μ (closed_ball x ε)) := Ennreal.mul_left_mono (hε.2 x)
      _ = ↑(C ^ (n + 1)) * μ (closed_ball x ε) := by rw [← mul_assoc, pow_succ', Ennreal.coe_mul]
      
  rcases lt_or_le K 1 with (hK | hK)
  · refine' ⟨1, _⟩
    simp only [Ennreal.coe_one, one_mul]
    exact
      eventually_mem_nhds_within.mono fun ε hε x t ht =>
        measure_mono $ closed_ball_subset_closed_ball (by nlinarith [mem_Ioi.mp hε])
    
  · refine'
      ⟨C ^ ⌈Real.logb 2 K⌉₊,
        ((hμ ⌈Real.logb 2 K⌉₊).And eventually_mem_nhds_within).mono fun ε hε x t ht =>
          le_trans (measure_mono $ closed_ball_subset_closed_ball _) (hε.1 x)⟩
    refine' mul_le_mul_of_nonneg_right (ht.trans _) (mem_Ioi.mp hε.2).le
    conv_lhs => rw [← Real.rpow_logb two_pos (by norm_num) (by linarith : 0 < K)]
    rw [← Real.rpow_nat_cast]
    exact Real.rpow_le_rpow_of_exponent_le one_le_two (Nat.le_ceil (Real.logb 2 K))
    
#align
  is_doubling_measure.exists_eventually_forall_measure_closed_ball_le_mul IsDoublingMeasure.exists_eventually_forall_measure_closed_ball_le_mul

/-- A variant of `is_doubling_measure.doubling_constant` which allows for scaling the radius by
values other than `2`. -/
def scalingConstantOf (K : ℝ) : ℝ≥0 :=
  max (Classical.choose $ exists_eventually_forall_measure_closed_ball_le_mul μ K) 1
#align is_doubling_measure.scaling_constant_of IsDoublingMeasure.scalingConstantOf

theorem eventually_measure_mul_le_scaling_constant_of_mul (K : ℝ) :
    ∃ R : ℝ,
      0 < R ∧
        ∀ (x t r) (ht : t ∈ ioc 0 K) (hr : r ≤ R),
          μ (closedBall x (t * r)) ≤ scalingConstantOf μ K * μ (closedBall x r) :=
  by
  have h := Classical.choose_spec (exists_eventually_forall_measure_closed_ball_le_mul μ K)
  rcases mem_nhds_within_Ioi_iff_exists_Ioc_subset.1 h with ⟨R, Rpos, hR⟩
  refine' ⟨R, Rpos, fun x t r ht hr => _⟩
  rcases lt_trichotomy r 0 with (rneg | rfl | rpos)
  · have : t * r < 0 := mul_neg_of_pos_of_neg ht.1 rneg
    simp only [closed_ball_eq_empty.2 this, measure_empty, zero_le']
    
  · simp only [mul_zero, closed_ball_zero]
    refine' le_mul_of_one_le_of_le _ le_rfl
    apply Ennreal.one_le_coe_iff.2 (le_max_right _ _)
    
  · apply (hR ⟨rpos, hr⟩ x t ht.2).trans _
    exact Ennreal.mul_le_mul (Ennreal.coe_le_coe.2 (le_max_left _ _)) le_rfl
    
#align
  is_doubling_measure.eventually_measure_mul_le_scaling_constant_of_mul IsDoublingMeasure.eventually_measure_mul_le_scaling_constant_of_mul

/-- A scale below which the doubling measure `μ` satisfies good rescaling properties when one
multiplies the radius of balls by at most `K`, as stated
in `measure_mul_le_scaling_constant_of_mul`. -/
def scalingScaleOf (K : ℝ) : ℝ :=
  (eventually_measure_mul_le_scaling_constant_of_mul μ K).some
#align is_doubling_measure.scaling_scale_of IsDoublingMeasure.scalingScaleOf

theorem scaling_scale_of_pos (K : ℝ) : 0 < scalingScaleOf μ K :=
  (eventually_measure_mul_le_scaling_constant_of_mul μ K).some_spec.1
#align is_doubling_measure.scaling_scale_of_pos IsDoublingMeasure.scaling_scale_of_pos

theorem measure_mul_le_scaling_constant_of_mul {K : ℝ} {x : α} {t r : ℝ} (ht : t ∈ ioc 0 K)
    (hr : r ≤ scalingScaleOf μ K) : μ (closedBall x (t * r)) ≤ scalingConstantOf μ K * μ (closedBall x r) :=
  (eventually_measure_mul_le_scaling_constant_of_mul μ K).some_spec.2 x t r ht hr
#align
  is_doubling_measure.measure_mul_le_scaling_constant_of_mul IsDoublingMeasure.measure_mul_le_scaling_constant_of_mul

end IsDoublingMeasure

