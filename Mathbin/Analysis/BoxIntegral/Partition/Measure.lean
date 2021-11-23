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

noncomputable theory

open_locale Ennreal BigOperators Classical BoxIntegral

variable{ι : Type _}

namespace BoxIntegral

open MeasureTheory

namespace Box

variable(I : box ι)

-- error in Analysis.BoxIntegral.Partition.Measure: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem measurable_set_coe [fintype ι] (I : box ι) : measurable_set (I : set (ι → exprℝ())) :=
begin
  rw ["[", expr coe_eq_pi, "]"] [],
  haveI [] [] [":=", expr fintype.encodable ι],
  exact [expr measurable_set.univ_pi (λ i, measurable_set_Ioc)]
end

theorem measurable_set_Icc [Fintype ι] (I : box ι) : MeasurableSet I.Icc :=
  measurable_set_Icc

theorem measure_Icc_lt_top (μ : Measureₓ (ι → ℝ)) [is_locally_finite_measure μ] : μ I.Icc < ∞ :=
  show μ (Icc I.lower I.upper) < ∞ from I.is_compact_Icc.measure_lt_top

theorem measure_coe_lt_top (μ : Measureₓ (ι → ℝ)) [is_locally_finite_measure μ] : μ I < ∞ :=
  (measure_mono$ coe_subset_Icc).trans_lt (I.measure_Icc_lt_top μ)

end Box

theorem prepartition.measure_Union_to_real [Fintype ι] {I : box ι} (π : prepartition I) (μ : Measureₓ (ι → ℝ))
  [is_locally_finite_measure μ] : (μ π.Union).toReal = ∑J in π.boxes, (μ J).toReal :=
  by 
    erw [←Ennreal.to_real_sum, π.Union_def, measure_bUnion_finset π.pairwise_disjoint]
    exacts[fun J hJ => J.measurable_set_coe, fun J hJ => (J.measure_coe_lt_top μ).Ne]

end BoxIntegral

open BoxIntegral BoxIntegral.Box

variable[Fintype ι]

namespace MeasureTheory

namespace Measureₓ

/-- If `μ` is a locally finite measure on `ℝⁿ`, then `λ J, (μ J).to_real` is a box-additive
function. -/
@[simps]
def to_box_additive (μ : Measureₓ (ι → ℝ)) [is_locally_finite_measure μ] : ι →ᵇᵃ[⊤] ℝ :=
  { toFun := fun J => (μ J).toReal,
    sum_partition_boxes' :=
      fun J hJ π hπ =>
        by 
          rw [←π.measure_Union_to_real, hπ.Union_eq] }

end Measureₓ

end MeasureTheory

namespace BoxIntegral

open MeasureTheory

namespace Box

@[simp]
theorem volume_apply (I : box ι) : (volume : Measureₓ (ι → ℝ)).toBoxAdditive I = ∏i, I.upper i - I.lower i :=
  by 
    rw [measure.to_box_additive_apply, coe_eq_pi, Real.volume_pi_Ioc_to_real I.lower_le_upper]

theorem volume_face_mul {n} (i : Finₓ (n+1)) (I : box (Finₓ (n+1))) :
  ((∏j, (I.face i).upper j - (I.face i).lower j)*I.upper i - I.lower i) = ∏j, I.upper j - I.lower j :=
  by 
    simp only [face_lower, face_upper, · ∘ ·, Finₓ.prod_univ_succ_above _ i, mul_commₓ]

end Box

namespace BoxAdditiveMap

/-- Box-additive map sending each box `I` to the continuous linear endomorphism
`x ↦ (volume I).to_real • x`. -/
protected def volume {E : Type _} [NormedGroup E] [NormedSpace ℝ E] : ι →ᵇᵃ E →L[ℝ] E :=
  (volume : Measureₓ (ι → ℝ)).toBoxAdditive.toSmul

theorem volume_apply {E : Type _} [NormedGroup E] [NormedSpace ℝ E] (I : box ι) (x : E) :
  box_additive_map.volume I x = (∏j, I.upper j - I.lower j) • x :=
  congr_arg2 (· • ·) I.volume_apply rfl

end BoxAdditiveMap

end BoxIntegral

