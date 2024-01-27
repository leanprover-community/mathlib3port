/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import MeasureTheory.Constructions.BorelSpace.Complex
import MeasureTheory.Measure.Lebesgue.Basic
import MeasureTheory.Measure.Haar.OfBasis

#align_import measure_theory.measure.lebesgue.complex from "leanprover-community/mathlib"@"af471b9e3ce868f296626d33189b4ce730fa4c00"

/-!
# Lebesgue measure on `ℂ`

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

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
instance measureSpace : MeasureSpace ℂ :=
  ⟨Measure.map basisOneI.equivFun.symm volume⟩
#align complex.measure_space Complex.measureSpace

#print Complex.measurableEquivPi /-
/-- Measurable equivalence between `ℂ` and `ℝ² = fin 2 → ℝ`. -/
def measurableEquivPi : ℂ ≃ᵐ (Fin 2 → ℝ) :=
  basisOneI.equivFun.toContinuousLinearEquiv.toHomeomorph.toMeasurableEquiv
#align complex.measurable_equiv_pi Complex.measurableEquivPi
-/

#print Complex.measurableEquivRealProd /-
/-- Measurable equivalence between `ℂ` and `ℝ × ℝ`. -/
def measurableEquivRealProd : ℂ ≃ᵐ ℝ × ℝ :=
  equivRealProdCLM.toHomeomorph.toMeasurableEquiv
#align complex.measurable_equiv_real_prod Complex.measurableEquivRealProd
-/

#print Complex.volume_preserving_equiv_pi /-
theorem volume_preserving_equiv_pi : MeasurePreserving measurableEquivPi :=
  (measurableEquivPi.symm.Measurable.MeasurePreserving _).symm _
#align complex.volume_preserving_equiv_pi Complex.volume_preserving_equiv_pi
-/

#print Complex.volume_preserving_equiv_real_prod /-
theorem volume_preserving_equiv_real_prod : MeasurePreserving measurableEquivRealProd :=
  (volume_preserving_finTwoArrow ℝ).comp volume_preserving_equiv_pi
#align complex.volume_preserving_equiv_real_prod Complex.volume_preserving_equiv_real_prod
-/

end Complex

