import Mathbin.MeasureTheory.Integral.Bochner
import Mathbin.MeasureTheory.Group.Measure

/-!
# Integration on Groups

We develop properties of integrals with a group as domain.
This file contains properties about integrability, Lebesgue integration and Bochner integration.
-/


namespace MeasureTheory

open Measureₓ TopologicalSpace

open_locale Ennreal

variable {𝕜 G E : Type _} [MeasurableSpace G] {μ : Measure G}

variable [NormedGroup E] [SecondCountableTopology E] [NormedSpace ℝ E] [CompleteSpace E] [MeasurableSpace E]
  [BorelSpace E]

section MeasurableMul

variable [Groupₓ G] [HasMeasurableMul G]

/-- Translating a function by left-multiplication does not change its `lintegral` with respect to
a left-invariant measure. -/
@[to_additive]
theorem lintegral_mul_left_eq_self [IsMulLeftInvariant μ] (f : G → ℝ≥0∞) (g : G) :
    (∫⁻ x, f (g * x) ∂μ) = ∫⁻ x, f x ∂μ := by
  convert (lintegral_map_equiv f <| MeasurableEquiv.mulLeft g).symm
  simp [map_mul_left_eq_self μ g]

/-- Translating a function by right-multiplication does not change its `lintegral` with respect to
a right-invariant measure. -/
@[to_additive]
theorem lintegral_mul_right_eq_self [IsMulRightInvariant μ] (f : G → ℝ≥0∞) (g : G) :
    (∫⁻ x, f (x * g) ∂μ) = ∫⁻ x, f x ∂μ := by
  convert (lintegral_map_equiv f <| MeasurableEquiv.mulRight g).symm
  simp [map_mul_right_eq_self μ g]

/-- Translating a function by left-multiplication does not change its integral with respect to a
left-invariant measure. -/
@[to_additive]
theorem integral_mul_left_eq_self [IsMulLeftInvariant μ] (f : G → E) (g : G) : (∫ x, f (g * x) ∂μ) = ∫ x, f x ∂μ := by
  have h_mul : MeasurableEmbedding fun x => g * x := (MeasurableEquiv.mulLeft g).MeasurableEmbedding
  rw [← h_mul.integral_map, map_mul_left_eq_self]

/-- Translating a function by right-multiplication does not change its integral with respect to a
right-invariant measure. -/
@[to_additive]
theorem integral_mul_right_eq_self [IsMulRightInvariant μ] (f : G → E) (g : G) : (∫ x, f (x * g) ∂μ) = ∫ x, f x ∂μ := by
  have h_mul : MeasurableEmbedding fun x => x * g := (MeasurableEquiv.mulRight g).MeasurableEmbedding
  rw [← h_mul.integral_map, map_mul_right_eq_self]

/-- If some left-translate of a function negates it, then the integral of the function with respect
to a left-invariant measure is 0. -/
@[to_additive]
theorem integral_zero_of_mul_left_eq_neg [IsMulLeftInvariant μ] {f : G → E} {g : G} (hf' : ∀ x, f (g * x) = -f x) :
    (∫ x, f x ∂μ) = 0 := by
  simp_rw [← self_eq_neg ℝ E, ← integral_neg, ← hf', integral_mul_left_eq_self]

/-- If some right-translate of a function negates it, then the integral of the function with respect
to a right-invariant measure is 0. -/
@[to_additive]
theorem integral_zero_of_mul_right_eq_neg [IsMulRightInvariant μ] {f : G → E} {g : G} (hf' : ∀ x, f (x * g) = -f x) :
    (∫ x, f x ∂μ) = 0 := by
  simp_rw [← self_eq_neg ℝ E, ← integral_neg, ← hf', integral_mul_right_eq_self]

end MeasurableMul

section TopologicalGroup

variable [TopologicalSpace G] [Groupₓ G] [TopologicalGroup G] [BorelSpace G] [IsMulLeftInvariant μ]

/-- For nonzero regular left invariant measures, the integral of a continuous nonnegative function
  `f` is 0 iff `f` is 0. -/
@[to_additive]
theorem lintegral_eq_zero_of_is_mul_left_invariant [Regular μ] (hμ : μ ≠ 0) {f : G → ℝ≥0∞} (hf : Continuous f) :
    (∫⁻ x, f x ∂μ) = 0 ↔ f = 0 := by
  have := is_open_pos_measure_of_mul_left_invariant_of_regular hμ
  rw [lintegral_eq_zero_iff hf.measurable, hf.ae_eq_iff_eq μ continuous_zero]

end TopologicalGroup

end MeasureTheory

