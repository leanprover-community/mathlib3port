/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathbin.Analysis.BoxIntegral.Partition.Additive
import Mathbin.MeasureTheory.Measure.Lebesgue

/-!
# Box-additive functions defined by measures

In this file we prove a few simple facts about rectangular boxes, partitions, and measures:

- given a box `I : box ι`, its coercion to `set (ι → ℝ)` and `I.Icc` are measurable sets;
- if `μ` is a locally finite measure, then `(I : set (ι → ℝ))` and `I.Icc` have finite measure;
- if `μ` is a locally finite measure, then `λ J, (μ J).to_real` is a box additive function.

For the last statement, we both prove it as a proposition and define a bundled
`box_integral.box_additive` function.

### Tags

rectangular box, measure
-/


open Set

noncomputable section

open Ennreal BigOperators Classical BoxIntegral

variable {ι : Type _}

namespace BoxIntegral

open MeasureTheory

namespace Box

variable (I : Box ι)

theorem measure_Icc_lt_top (μ : Measure (ι → ℝ)) [IsLocallyFiniteMeasure μ] : μ I.IccCat < ∞ :=
  show μ (IccCat I.lower I.upper) < ∞ from I.is_compact_Icc.measure_lt_top

theorem measure_coe_lt_top (μ : Measure (ι → ℝ)) [IsLocallyFiniteMeasure μ] : μ I < ∞ :=
  (measure_mono <| coe_subset_Icc).trans_lt (I.measure_Icc_lt_top μ)

section Countable

variable [Countable ι]

theorem measurableSetCoe : MeasurableSet (I : Set (ι → ℝ)) := by
  rw [coe_eq_pi]
  exact MeasurableSet.univPi fun i => measurableSetIoc

theorem measurableSetIcc : MeasurableSet I.IccCat :=
  measurableSetIcc

theorem measurableSetIoo : MeasurableSet I.IooCat :=
  MeasurableSet.univPi fun i => measurableSetIoo

end Countable

variable [Fintype ι]

theorem coe_ae_eq_Icc : (I : Set (ι → ℝ)) =ᵐ[volume] I.IccCat := by
  rw [coe_eq_pi]
  exact measure.univ_pi_Ioc_ae_eq_Icc

theorem Ioo_ae_eq_Icc : I.IooCat =ᵐ[volume] I.IccCat :=
  measure.univ_pi_Ioo_ae_eq_Icc

end Box

theorem Prepartition.measure_Union_to_real [Finite ι] {I : Box ι} (π : Prepartition I) (μ : Measure (ι → ℝ))
    [IsLocallyFiniteMeasure μ] : (μ π.UnionCat).toReal = ∑ J in π.boxes, (μ J).toReal := by
  erw [← Ennreal.to_real_sum, π.Union_def, measure_bUnion_finset π.pairwise_disjoint]
  exacts[fun J hJ => J.measurableSetCoe, fun J hJ => (J.measure_coe_lt_top μ).Ne]

end BoxIntegral

open BoxIntegral BoxIntegral.Box

variable [Fintype ι]

namespace MeasureTheory

namespace Measure

/-- If `μ` is a locally finite measure on `ℝⁿ`, then `λ J, (μ J).to_real` is a box-additive
function. -/
@[simps]
def toBoxAdditive (μ : Measure (ι → ℝ)) [IsLocallyFiniteMeasure μ] : ι →ᵇᵃ[⊤] ℝ where
  toFun J := (μ J).toReal
  sum_partition_boxes' J hJ π hπ := by rw [← π.measure_Union_to_real, hπ.Union_eq]

end Measure

end MeasureTheory

namespace BoxIntegral

open MeasureTheory

namespace Box

@[simp]
theorem volume_apply (I : Box ι) : (volume : Measure (ι → ℝ)).toBoxAdditive I = ∏ i, I.upper i - I.lower i := by
  rw [measure.to_box_additive_apply, coe_eq_pi, Real.volume_pi_Ioc_to_real I.lower_le_upper]

theorem volume_face_mul {n} (i : Fin (n + 1)) (I : Box (Fin (n + 1))) :
    (∏ j, (I.face i).upper j - (I.face i).lower j) * (I.upper i - I.lower i) = ∏ j, I.upper j - I.lower j := by
  simp only [face_lower, face_upper, (· ∘ ·), Fin.prod_univ_succ_above _ i, mul_comm]

end Box

namespace BoxAdditiveMap

/-- Box-additive map sending each box `I` to the continuous linear endomorphism
`x ↦ (volume I).to_real • x`. -/
protected def volume {E : Type _} [NormedAddCommGroup E] [NormedSpace ℝ E] : ι →ᵇᵃ E →L[ℝ] E :=
  (volume : Measure (ι → ℝ)).toBoxAdditive.toSmul

theorem volume_apply {E : Type _} [NormedAddCommGroup E] [NormedSpace ℝ E] (I : Box ι) (x : E) :
    BoxAdditiveMap.volume I x = (∏ j, I.upper j - I.lower j) • x :=
  congr_arg₂ (· • ·) I.volume_apply rfl

end BoxAdditiveMap

end BoxIntegral

