import Mathbin.MeasureTheory.Measure.Lebesgue

/-!
# Lebesgue measure on `ℂ`

In this file we define Lebesgue measure on `ℂ`. Since `ℂ` is defined as a `structure` as the
push-forward of the volume on `ℝ²` under the natural isomorphism. There are (at least) two
frequently used ways to represent `ℝ²` in `mathlib`: `ℝ × ℝ` and `fin 2 → ℝ`. We define measurable
equivalences (`measurable_equiv`) to both types and prove that both of them are volume preserving
(in the sense of `measure_theory.measure_preserving`).
-/


open MeasureTheory

noncomputable section

namespace Complex

/-- Lebesgue measure on `ℂ`. -/
instance measure_space : MeasureSpace ℂ :=
  ⟨Measure.map basisOneI.equivFun.symm volume⟩

/-- Measurable equivalence between `ℂ` and `ℝ² = fin 2 → ℝ`. -/
def measurable_equiv_pi : ℂ ≃ᵐ (Finₓ 2 → ℝ) :=
  basisOneI.equivFun.toContinuousLinearEquiv.toHomeomorph.toMeasurableEquiv

/-- Measurable equivalence between `ℂ` and `ℝ × ℝ`. -/
def measurable_equiv_real_prod : ℂ ≃ᵐ ℝ × ℝ :=
  equivRealProdₗ.toHomeomorph.toMeasurableEquiv

theorem volume_preserving_equiv_pi : MeasurePreserving measurableEquivPi :=
  (measurableEquivPi.symm.Measurable.MeasurePreserving _).symm

theorem volume_preserving_equiv_real_prod : MeasurePreserving measurableEquivRealProd :=
  (volume_preserving_fin_two_arrow ℝ).comp volume_preserving_equiv_pi

end Complex

