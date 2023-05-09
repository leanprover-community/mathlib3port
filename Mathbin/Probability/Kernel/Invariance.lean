/-
Copyright (c) 2023 Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kexing Ying

! This file was ported from Lean 3 source module probability.kernel.invariance
! leanprover-community/mathlib commit a9545e8a564bac7f24637443f52ae955474e4991
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Probability.Kernel.Composition

/-!
# Invariance of measures along a kernel

We define the push-forward of a measure along a kernel which results in another measure. In the
case that the push-forward measure is the same as the original measure, we say that the measure is
invariant with respect to the kernel.

## Main definitions

* `probability_theory.kernel.map_measure`: the push-forward of a measure along a kernel.
* `probability_theory.kernel.invariant`: invariance of a given measure with respect to a kernel.

## Useful lemmas

* `probability_theory.kernel.comp_apply_eq_map_measure`,
  `probability_theory.kernel.const_map_measure_eq_comp_const`, and
  `probability_theory.kernel.comp_const_apply_eq_map_measure` established the relationship between
  the push-forward measure and the composition of kernels.

-/


open MeasureTheory

open MeasureTheory ENNReal ProbabilityTheory

namespace ProbabilityTheory

variable {α β γ : Type _} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {mγ : MeasurableSpace γ}

include mα mβ

namespace Kernel

/-! ### Push-forward of measures along a kernel -/


/-- The push-forward of a measure along a kernel. -/
noncomputable def mapMeasure (κ : kernel α β) (μ : Measure α) : Measure β :=
  Measure.ofMeasurable (fun s hs => ∫⁻ x, κ x s ∂μ)
    (by simp only [measure_empty, MeasureTheory.lintegral_const, MulZeroClass.zero_mul])
    (by
      intro f hf₁ hf₂
      simp_rw [measure_Union hf₂ hf₁,
        lintegral_tsum fun i => (kernel.measurable_coe κ (hf₁ i)).AEMeasurable])
#align probability_theory.kernel.map_measure ProbabilityTheory.kernel.mapMeasure

@[simp]
theorem mapMeasure_apply (κ : kernel α β) (μ : Measure α) {s : Set β} (hs : MeasurableSet s) :
    mapMeasure κ μ s = ∫⁻ x, κ x s ∂μ := by rw [map_measure, measure.of_measurable_apply s hs]
#align probability_theory.kernel.map_measure_apply ProbabilityTheory.kernel.mapMeasure_apply

@[simp]
theorem mapMeasure_zero (κ : kernel α β) : mapMeasure κ 0 = 0 :=
  by
  ext1 s hs
  rw [map_measure_apply κ 0 hs, lintegral_zero_measure, measure.coe_zero, Pi.zero_apply]
#align probability_theory.kernel.map_measure_zero ProbabilityTheory.kernel.mapMeasure_zero

@[simp]
theorem mapMeasure_add (κ : kernel α β) (μ ν : Measure α) :
    mapMeasure κ (μ + ν) = mapMeasure κ μ + mapMeasure κ ν :=
  by
  ext1 s hs
  rw [map_measure_apply κ (μ + ν) hs, lintegral_add_measure, measure.coe_add, Pi.add_apply,
    map_measure_apply κ μ hs, map_measure_apply κ ν hs]
#align probability_theory.kernel.map_measure_add ProbabilityTheory.kernel.mapMeasure_add

@[simp]
theorem mapMeasure_smul (κ : kernel α β) (μ : Measure α) (r : ℝ≥0∞) :
    mapMeasure κ (r • μ) = r • mapMeasure κ μ :=
  by
  ext1 s hs
  rw [map_measure_apply κ (r • μ) hs, lintegral_smul_measure, measure.coe_smul, Pi.smul_apply,
    map_measure_apply κ μ hs, smul_eq_mul]
#align probability_theory.kernel.map_measure_smul ProbabilityTheory.kernel.mapMeasure_smul

include mγ

theorem comp_apply_eq_mapMeasure (η : kernel β γ) [IsSFiniteKernel η] (κ : kernel α β)
    [IsSFiniteKernel κ] (a : α) : (η ∘ₖ κ) a = mapMeasure η (κ a) :=
  by
  ext1 s hs
  rw [comp_apply η κ a hs, map_measure_apply η _ hs]
#align probability_theory.kernel.comp_apply_eq_map_measure ProbabilityTheory.kernel.comp_apply_eq_mapMeasure

omit mγ

theorem const_mapMeasure_eq_comp_const (κ : kernel α β) [IsSFiniteKernel κ] (μ : Measure α)
    [IsFiniteMeasure μ] : const α (mapMeasure κ μ) = κ ∘ₖ const α μ :=
  by
  ext1 a; ext1 s hs
  rw [const_apply, map_measure_apply _ _ hs, comp_apply _ _ _ hs, const_apply]
#align probability_theory.kernel.const_map_measure_eq_comp_const ProbabilityTheory.kernel.const_mapMeasure_eq_comp_const

theorem comp_const_apply_eq_mapMeasure (κ : kernel α β) [IsSFiniteKernel κ] (μ : Measure α)
    [IsFiniteMeasure μ] (a : α) : (κ ∘ₖ const α μ) a = mapMeasure κ μ := by
  rw [← const_apply (map_measure κ μ) a, const_map_measure_eq_comp_const κ μ]
#align probability_theory.kernel.comp_const_apply_eq_map_measure ProbabilityTheory.kernel.comp_const_apply_eq_mapMeasure

theorem lintegral_mapMeasure (κ : kernel α β) [IsSFiniteKernel κ] (μ : Measure α)
    [IsFiniteMeasure μ] {f : β → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ b, f b ∂mapMeasure κ μ) = ∫⁻ a, ∫⁻ b, f b ∂κ a ∂μ :=
  by
  by_cases hα : Nonempty α
  · have := const_apply μ hα.some
    swap
    infer_instance
    conv_rhs => rw [← this]
    rw [← lintegral_comp _ _ _ hf, ← comp_const_apply_eq_map_measure κ μ hα.some]
  · haveI := not_nonempty_iff.1 hα
    rw [μ.eq_zero_of_is_empty, map_measure_zero, lintegral_zero_measure, lintegral_zero_measure]
#align probability_theory.kernel.lintegral_map_measure ProbabilityTheory.kernel.lintegral_mapMeasure

omit mβ

/-! ### Invariant measures of kernels -/


/-- A measure `μ` is invariant with respect to the kernel `κ` if the push-forward measure of `μ`
along `κ` equals `μ`. -/
def Invariant (κ : kernel α α) (μ : Measure α) : Prop :=
  mapMeasure κ μ = μ
#align probability_theory.kernel.invariant ProbabilityTheory.kernel.Invariant

variable {κ η : kernel α α} {μ : Measure α}

theorem Invariant.def (hκ : Invariant κ μ) : mapMeasure κ μ = μ :=
  hκ
#align probability_theory.kernel.invariant.def ProbabilityTheory.kernel.Invariant.def

theorem Invariant.comp_const [IsSFiniteKernel κ] [IsFiniteMeasure μ] (hκ : Invariant κ μ) :
    κ ∘ₖ const α μ = const α μ := by rw [← const_map_measure_eq_comp_const κ μ, hκ.def]
#align probability_theory.kernel.invariant.comp_const ProbabilityTheory.kernel.Invariant.comp_const

theorem Invariant.comp [IsSFiniteKernel κ] [IsSFiniteKernel η] [IsFiniteMeasure μ]
    (hκ : Invariant κ μ) (hη : Invariant η μ) : Invariant (κ ∘ₖ η) μ :=
  by
  by_cases hα : Nonempty α
  ·
    simp_rw [invariant, ← comp_const_apply_eq_map_measure (κ ∘ₖ η) μ hα.some, comp_assoc,
      hη.comp_const, hκ.comp_const, const_apply]
  · haveI := not_nonempty_iff.1 hα
    exact Subsingleton.elim _ _
#align probability_theory.kernel.invariant.comp ProbabilityTheory.kernel.Invariant.comp

end Kernel

end ProbabilityTheory

