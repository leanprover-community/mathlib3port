/-
Copyright (c) 2022 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov, Yaël Dillies

! This file was ported from Lean 3 source module measure_theory.integral.average
! leanprover-community/mathlib commit ccdbfb6e5614667af5aa3ab2d50885e0ef44a46f
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.MeasureTheory.Integral.SetIntegral

/-!
# Integral average of a function

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In this file we define `measure_theory.average μ f` (notation: `⨍ x, f x ∂μ`) to be the average
value of `f` with respect to measure `μ`. It is defined as `∫ x, f x ∂((μ univ)⁻¹ • μ)`, so it
is equal to zero if `f` is not integrable or if `μ` is an infinite measure. If `μ` is a probability
measure, then the average of any function is equal to its integral.

For the average on a set, we use `⨍ x in s, f x ∂μ` (notation for `⨍ x, f x ∂(μ.restrict s)`). For
average w.r.t. the volume, one can omit `∂volume`.

We prove several version of the first moment method: An integrable function is below/above its
average on a set of positive measure.

## Implementation notes

The average is defined as an integral over `(μ univ)⁻¹ • μ` so that all theorems about Bochner
integrals work for the average without modifications. For theorems that require integrability of a
function, we provide a convenience lemma `measure_theory.integrable.to_average`.

## TODO

Provide the first moment method for the Lebesgue integral as well. A draft is available on branch
`first_moment_lintegral`.

## Tags

integral, center mass, average value
-/


open ENNReal MeasureTheory MeasureTheory.Measure Metric Set Filter TopologicalSpace Function

open scoped Topology BigOperators ENNReal Convex

variable {α E F : Type _} {m0 : MeasurableSpace α} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] {μ : Measure α}
  {s t : Set α}

/-!
### Average value of a function w.r.t. a measure

The average value of a function `f` w.r.t. a measure `μ` (notation: `⨍ x, f x ∂μ`) is defined as
`(μ univ).to_real⁻¹ • ∫ x, f x ∂μ`, so it is equal to zero if `f` is not integrable or if `μ` is an
infinite measure. If `μ` is a probability measure, then the average of any function is equal to its
integral.

-/


namespace MeasureTheory

section NormedAddCommGroup

variable (μ) {f g : α → E}

#print MeasureTheory.average /-
/-- Average value of a function `f` w.r.t. a measure `μ`, notation: `⨍ x, f x ∂μ`. It is defined as
`(μ univ).to_real⁻¹ • ∫ x, f x ∂μ`, so it is equal to zero if `f` is not integrable or if `μ` is an
infinite measure. If `μ` is a probability measure, then the average of any function is equal to its
integral.

For the average on a set, use `⨍ x in s, f x ∂μ` (defined as `⨍ x, f x ∂(μ.restrict s)`). For
average w.r.t. the volume, one can omit `∂volume`. -/
noncomputable def average (f : α → E) :=
  ∫ x, f x ∂(μ univ)⁻¹ • μ
#align measure_theory.average MeasureTheory.average
-/

notation3"⨍ "(...)", "r:60:(scoped f => f)" ∂"μ:70 => average μ r

notation3"⨍ "(...)", "r:60:(scoped f => average volume f) => r

notation3"⨍ "(...)" in "s", "r:60:(scoped f => f)" ∂"μ:70 => average (Measure.restrict μ s) r

notation3"⨍ "(...)" in "s", "r:60:(scoped f => average Measure.restrict volume s f) => r

#print MeasureTheory.average_zero /-
@[simp]
theorem average_zero : ⨍ x, (0 : E) ∂μ = 0 := by rw [average, integral_zero]
#align measure_theory.average_zero MeasureTheory.average_zero
-/

#print MeasureTheory.average_zero_measure /-
@[simp]
theorem average_zero_measure (f : α → E) : ⨍ x, f x ∂(0 : Measure α) = 0 := by
  rw [average, smul_zero, integral_zero_measure]
#align measure_theory.average_zero_measure MeasureTheory.average_zero_measure
-/

#print MeasureTheory.average_neg /-
@[simp]
theorem average_neg (f : α → E) : ⨍ x, -f x ∂μ = -⨍ x, f x ∂μ :=
  integral_neg f
#align measure_theory.average_neg MeasureTheory.average_neg
-/

#print MeasureTheory.average_eq' /-
theorem average_eq' (f : α → E) : ⨍ x, f x ∂μ = ∫ x, f x ∂(μ univ)⁻¹ • μ :=
  rfl
#align measure_theory.average_eq' MeasureTheory.average_eq'
-/

#print MeasureTheory.average_eq /-
theorem average_eq (f : α → E) : ⨍ x, f x ∂μ = (μ univ).toReal⁻¹ • ∫ x, f x ∂μ := by
  rw [average_eq', integral_smul_measure, ENNReal.toReal_inv]
#align measure_theory.average_eq MeasureTheory.average_eq
-/

#print MeasureTheory.average_eq_integral /-
theorem average_eq_integral [IsProbabilityMeasure μ] (f : α → E) : ⨍ x, f x ∂μ = ∫ x, f x ∂μ := by
  rw [average, measure_univ, inv_one, one_smul]
#align measure_theory.average_eq_integral MeasureTheory.average_eq_integral
-/

#print MeasureTheory.measure_smul_average /-
@[simp]
theorem measure_smul_average [IsFiniteMeasure μ] (f : α → E) :
    (μ univ).toReal • ⨍ x, f x ∂μ = ∫ x, f x ∂μ :=
  by
  cases' eq_or_ne μ 0 with hμ hμ
  · rw [hμ, integral_zero_measure, average_zero_measure, smul_zero]
  · rw [average_eq, smul_inv_smul₀]
    refine' (ENNReal.toReal_pos _ <| measure_ne_top _ _).ne'
    rwa [Ne.def, measure_univ_eq_zero]
#align measure_theory.measure_smul_average MeasureTheory.measure_smul_average
-/

#print MeasureTheory.set_average_eq /-
theorem set_average_eq (f : α → E) (s : Set α) :
    ⨍ x in s, f x ∂μ = (μ s).toReal⁻¹ • ∫ x in s, f x ∂μ := by rw [average_eq, restrict_apply_univ]
#align measure_theory.set_average_eq MeasureTheory.set_average_eq
-/

#print MeasureTheory.set_average_eq' /-
theorem set_average_eq' (f : α → E) (s : Set α) :
    ⨍ x in s, f x ∂μ = ∫ x, f x ∂(μ s)⁻¹ • μ.restrict s := by
  simp only [average_eq', restrict_apply_univ]
#align measure_theory.set_average_eq' MeasureTheory.set_average_eq'
-/

variable {μ}

#print MeasureTheory.average_congr /-
theorem average_congr {f g : α → E} (h : f =ᵐ[μ] g) : ⨍ x, f x ∂μ = ⨍ x, g x ∂μ := by
  simp only [average_eq, integral_congr_ae h]
#align measure_theory.average_congr MeasureTheory.average_congr
-/

theorem set_average_congr_set_ae (h : s =ᵐ[μ] t) : ⨍ x in s, f x ∂μ = ⨍ x in t, f x ∂μ := by
  simp only [set_average_eq, set_integral_congr_set_ae h, measure_congr h]
#align measure_theory.set_average_congr_set_ae MeasureTheory.set_average_congr_set_ae

#print MeasureTheory.average_add_measure /-
theorem average_add_measure [IsFiniteMeasure μ] {ν : Measure α} [IsFiniteMeasure ν] {f : α → E}
    (hμ : Integrable f μ) (hν : Integrable f ν) :
    ⨍ x, f x ∂(μ + ν) =
      ((μ univ).toReal / ((μ univ).toReal + (ν univ).toReal)) • ⨍ x, f x ∂μ +
        ((ν univ).toReal / ((μ univ).toReal + (ν univ).toReal)) • ⨍ x, f x ∂ν :=
  by
  simp only [div_eq_inv_mul, mul_smul, measure_smul_average, ← smul_add, ←
    integral_add_measure hμ hν, ← ENNReal.toReal_add (measure_ne_top μ _) (measure_ne_top ν _)]
  rw [average_eq, measure.add_apply]
#align measure_theory.average_add_measure MeasureTheory.average_add_measure
-/

#print MeasureTheory.average_pair /-
theorem average_pair {f : α → E} {g : α → F} (hfi : Integrable f μ) (hgi : Integrable g μ) :
    ⨍ x, (f x, g x) ∂μ = (⨍ x, f x ∂μ, ⨍ x, g x ∂μ) :=
  integral_pair hfi.to_average hgi.to_average
#align measure_theory.average_pair MeasureTheory.average_pair
-/

#print MeasureTheory.measure_smul_set_average /-
theorem measure_smul_set_average (f : α → E) {s : Set α} (h : μ s ≠ ∞) :
    (μ s).toReal • ⨍ x in s, f x ∂μ = ∫ x in s, f x ∂μ := by haveI := Fact.mk h.lt_top;
  rw [← measure_smul_average, restrict_apply_univ]
#align measure_theory.measure_smul_set_average MeasureTheory.measure_smul_set_average
-/

#print MeasureTheory.average_union /-
theorem average_union {f : α → E} {s t : Set α} (hd : AEDisjoint μ s t) (ht : NullMeasurableSet t μ)
    (hsμ : μ s ≠ ∞) (htμ : μ t ≠ ∞) (hfs : IntegrableOn f s μ) (hft : IntegrableOn f t μ) :
    ⨍ x in s ∪ t, f x ∂μ =
      ((μ s).toReal / ((μ s).toReal + (μ t).toReal)) • ⨍ x in s, f x ∂μ +
        ((μ t).toReal / ((μ s).toReal + (μ t).toReal)) • ⨍ x in t, f x ∂μ :=
  by
  haveI := Fact.mk hsμ.lt_top; haveI := Fact.mk htμ.lt_top
  rw [restrict_union₀ hd ht, average_add_measure hfs hft, restrict_apply_univ, restrict_apply_univ]
#align measure_theory.average_union MeasureTheory.average_union
-/

#print MeasureTheory.average_union_mem_openSegment /-
theorem average_union_mem_openSegment {f : α → E} {s t : Set α} (hd : AEDisjoint μ s t)
    (ht : NullMeasurableSet t μ) (hs₀ : μ s ≠ 0) (ht₀ : μ t ≠ 0) (hsμ : μ s ≠ ∞) (htμ : μ t ≠ ∞)
    (hfs : IntegrableOn f s μ) (hft : IntegrableOn f t μ) :
    ⨍ x in s ∪ t, f x ∂μ ∈ openSegment ℝ (⨍ x in s, f x ∂μ) (⨍ x in t, f x ∂μ) :=
  by
  replace hs₀ : 0 < (μ s).toReal; exact ENNReal.toReal_pos hs₀ hsμ
  replace ht₀ : 0 < (μ t).toReal; exact ENNReal.toReal_pos ht₀ htμ
  refine'
    mem_open_segment_iff_div.mpr
      ⟨(μ s).toReal, (μ t).toReal, hs₀, ht₀, (average_union hd ht hsμ htμ hfs hft).symm⟩
#align measure_theory.average_union_mem_open_segment MeasureTheory.average_union_mem_openSegment
-/

#print MeasureTheory.average_union_mem_segment /-
theorem average_union_mem_segment {f : α → E} {s t : Set α} (hd : AEDisjoint μ s t)
    (ht : NullMeasurableSet t μ) (hsμ : μ s ≠ ∞) (htμ : μ t ≠ ∞) (hfs : IntegrableOn f s μ)
    (hft : IntegrableOn f t μ) : ⨍ x in s ∪ t, f x ∂μ ∈ [⨍ x in s, f x ∂μ -[ℝ] ⨍ x in t, f x ∂μ] :=
  by
  by_cases hse : μ s = 0
  · rw [← ae_eq_empty] at hse 
    rw [restrict_congr_set (hse.union eventually_eq.rfl), empty_union]
    exact right_mem_segment _ _ _
  · refine'
      mem_segment_iff_div.mpr
        ⟨(μ s).toReal, (μ t).toReal, ENNReal.toReal_nonneg, ENNReal.toReal_nonneg, _,
          (average_union hd ht hsμ htμ hfs hft).symm⟩
    calc
      0 < (μ s).toReal := ENNReal.toReal_pos hse hsμ
      _ ≤ _ := le_add_of_nonneg_right ENNReal.toReal_nonneg
#align measure_theory.average_union_mem_segment MeasureTheory.average_union_mem_segment
-/

#print MeasureTheory.average_mem_openSegment_compl_self /-
theorem average_mem_openSegment_compl_self [IsFiniteMeasure μ] {f : α → E} {s : Set α}
    (hs : NullMeasurableSet s μ) (hs₀ : μ s ≠ 0) (hsc₀ : μ (sᶜ) ≠ 0) (hfi : Integrable f μ) :
    ⨍ x, f x ∂μ ∈ openSegment ℝ (⨍ x in s, f x ∂μ) (⨍ x in sᶜ, f x ∂μ) := by
  simpa only [union_compl_self, restrict_univ] using
    average_union_mem_open_segment ae_disjoint_compl_right hs.compl hs₀ hsc₀ (measure_ne_top _ _)
      (measure_ne_top _ _) hfi.integrable_on hfi.integrable_on
#align measure_theory.average_mem_open_segment_compl_self MeasureTheory.average_mem_openSegment_compl_self
-/

#print MeasureTheory.average_const /-
@[simp]
theorem average_const [IsFiniteMeasure μ] [h : μ.ae.ne_bot] (c : E) : ⨍ x, c ∂μ = c := by
  simp only [average_eq, integral_const, measure.restrict_apply, MeasurableSet.univ, one_smul,
    univ_inter, smul_smul, ← ENNReal.toReal_inv, ← ENNReal.toReal_mul, ENNReal.inv_mul_cancel,
    measure_ne_top μ univ, Ne.def, measure_univ_eq_zero, ae_ne_bot.1 h, not_false_iff,
    ENNReal.one_toReal]
#align measure_theory.average_const MeasureTheory.average_const
-/

#print MeasureTheory.set_average_const /-
theorem set_average_const {s : Set α} (hs₀ : μ s ≠ 0) (hs : μ s ≠ ∞) (c : E) : ⨍ x in s, c ∂μ = c :=
  by
  simp only [set_average_eq, integral_const, measure.restrict_apply, MeasurableSet.univ, univ_inter,
    smul_smul, ← ENNReal.toReal_inv, ← ENNReal.toReal_mul, ENNReal.inv_mul_cancel hs₀ hs,
    ENNReal.one_toReal, one_smul]
#align measure_theory.set_average_const MeasureTheory.set_average_const
-/

@[simp]
theorem integral_average (μ : Measure α) [IsFiniteMeasure μ] (f : α → E) :
    ∫ x, ⨍ a, f a ∂μ ∂μ = ∫ x, f x ∂μ :=
  by
  obtain rfl | hμ := eq_or_ne μ 0
  · simp only [integral_zero_measure]
  ·
    rw [integral_const, average_eq,
      smul_inv_smul₀ (to_real_ne_zero.2 ⟨measure_univ_ne_zero.2 hμ, measure_ne_top _ _⟩)]
#align measure_theory.integral_average MeasureTheory.integral_average

theorem set_integral_set_average (μ : Measure α) [IsFiniteMeasure μ] (f : α → E) (s : Set α) :
    ∫ x in s, ⨍ a in s, f a ∂μ ∂μ = ∫ x in s, f x ∂μ :=
  integral_average _ _
#align measure_theory.set_integral_set_average MeasureTheory.set_integral_set_average

theorem integral_sub_average (μ : Measure α) [IsFiniteMeasure μ] (f : α → E) :
    ∫ x, f x - ⨍ a, f a ∂μ ∂μ = 0 :=
  by
  by_cases hf : integrable f μ
  · rw [integral_sub hf (integrable_const _), integral_average, sub_self]
  refine' integral_undef fun h => hf _
  convert h.add (integrable_const _)
  exact (sub_add_cancel _ _).symm
#align measure_theory.integral_sub_average MeasureTheory.integral_sub_average

theorem set_integral_sub_set_average (hs : μ s ≠ ∞) (f : α → E) :
    ∫ x in s, f x - ⨍ a in s, f a ∂μ ∂μ = 0 :=
  haveI haveI : Fact (μ s < ∞) := ⟨lt_top_iff_ne_top.2 hs⟩
  integral_sub_average _ _
#align measure_theory.set_integral_sub_set_average MeasureTheory.set_integral_sub_set_average

theorem integral_average_sub [IsFiniteMeasure μ] (hf : Integrable f μ) :
    ∫ x, ⨍ a, f a ∂μ - f x ∂μ = 0 := by
  rw [integral_sub (integrable_const _) hf, integral_average, sub_self]
#align measure_theory.integral_average_sub MeasureTheory.integral_average_sub

theorem set_integral_set_average_sub (hs : μ s ≠ ∞) (hf : IntegrableOn f s μ) :
    ∫ x in s, ⨍ a in s, f a ∂μ - f x ∂μ = 0 :=
  haveI haveI : Fact (μ s < ∞) := ⟨lt_top_iff_ne_top.2 hs⟩
  integral_average_sub hf
#align measure_theory.set_integral_set_average_sub MeasureTheory.set_integral_set_average_sub

end NormedAddCommGroup

theorem ofReal_average {f : α → ℝ} (hf : Integrable f μ) (hf₀ : 0 ≤ᵐ[μ] f) :
    ENNReal.ofReal (⨍ x, f x ∂μ) = (∫⁻ x, ENNReal.ofReal (f x) ∂μ) / μ univ :=
  by
  obtain rfl | hμ := eq_or_ne μ 0
  · simp
  ·
    rw [average_eq, smul_eq_mul, ← to_real_inv, of_real_mul to_real_nonneg,
      of_real_to_real (inv_ne_top.2 <| measure_univ_ne_zero.2 hμ),
      of_real_integral_eq_lintegral_of_real hf hf₀, ENNReal.div_eq_inv_mul]
#align measure_theory.of_real_average MeasureTheory.ofReal_average

theorem ofReal_set_average {f : α → ℝ} (hf : IntegrableOn f s μ) (hf₀ : 0 ≤ᵐ[μ.restrict s] f) :
    ENNReal.ofReal (⨍ x in s, f x ∂μ) = (∫⁻ x in s, ENNReal.ofReal (f x) ∂μ) / μ s := by
  simpa using of_real_average hf hf₀
#align measure_theory.of_real_set_average MeasureTheory.ofReal_set_average

theorem average_toReal {f : α → ℝ≥0∞} (hf : AEMeasurable f μ) (hf' : ∀ᵐ x ∂μ, f x ≠ ∞) :
    ⨍ x, (f x).toReal ∂μ = ((∫⁻ x, f x ∂μ) / μ univ).toReal :=
  by
  obtain rfl | hμ := eq_or_ne μ 0
  · simp
  ·
    rw [average_eq, smul_eq_mul, to_real_div, ←
      integral_to_real hf (hf'.mono fun _ => lt_top_iff_ne_top.2), div_eq_inv_mul]
#align measure_theory.average_to_real MeasureTheory.average_toReal

theorem set_average_toReal {f : α → ℝ≥0∞} (hf : AEMeasurable f (μ.restrict s))
    (hf' : ∀ᵐ x ∂μ.restrict s, f x ≠ ∞) :
    ⨍ x in s, (f x).toReal ∂μ = ((∫⁻ x in s, f x ∂μ) / μ s).toReal := by
  simpa using average_to_real hf hf'
#align measure_theory.set_average_to_real MeasureTheory.set_average_toReal

/-! ### First moment method -/


section FirstMoment

variable {N : Set α} {f : α → ℝ}

/-- **First moment method**. An integrable function is smaller than its mean on a set of positive
measure. -/
theorem measure_le_set_average_pos (hμ : μ s ≠ 0) (hμ₁ : μ s ≠ ∞) (hf : IntegrableOn f s μ) :
    0 < μ ({x ∈ s | f x ≤ ⨍ a in s, f a ∂μ}) :=
  by
  refine' pos_iff_ne_zero.2 fun H => _
  replace H : (μ.restrict s) {x | f x ≤ ⨍ a in s, f a ∂μ} = 0
  · rwa [restrict_apply₀, inter_comm]
    exact ae_strongly_measurable.null_measurable_set_le hf.1 ae_strongly_measurable_const
  haveI : is_finite_measure (μ.restrict s) :=
    ⟨by simpa only [measure.restrict_apply, MeasurableSet.univ, univ_inter] using hμ₁.lt_top⟩
  refine' (integral_sub_average (μ.restrict s) f).not_gt _
  refine' (set_integral_pos_iff_support_of_nonneg_ae _ _).2 _
  · refine' eq_bot_mono (measure_mono fun x hx => _) H
    simp only [Pi.zero_apply, sub_nonneg, mem_compl_iff, mem_set_of_eq, not_le] at hx 
    exact hx.le
  · exact hf.sub (integrable_on_const.2 <| Or.inr <| lt_top_iff_ne_top.2 hμ₁)
  · rwa [pos_iff_ne_zero, inter_comm, ← diff_compl, ← diff_inter_self_eq_diff, measure_diff_null]
    refine' eq_bot_mono (measure_mono _) (measure_inter_eq_zero_of_restrict H)
    exact inter_subset_inter_left _ fun a ha => (sub_eq_zero.1 <| of_not_not ha).le
#align measure_theory.measure_le_set_average_pos MeasureTheory.measure_le_set_average_pos

/-- **First moment method**. An integrable function is greater than its mean on a set of positive
measure. -/
theorem measure_set_average_le_pos (hμ : μ s ≠ 0) (hμ₁ : μ s ≠ ∞) (hf : IntegrableOn f s μ) :
    0 < μ ({x ∈ s | ⨍ a in s, f a ∂μ ≤ f x}) := by
  simpa [integral_neg, neg_div] using measure_le_set_average_pos hμ hμ₁ hf.neg
#align measure_theory.measure_set_average_le_pos MeasureTheory.measure_set_average_le_pos

/-- **First moment method**. The minimum of an integrable function is smaller than its mean. -/
theorem exists_le_set_average (hμ : μ s ≠ 0) (hμ₁ : μ s ≠ ∞) (hf : IntegrableOn f s μ) :
    ∃ x ∈ s, f x ≤ ⨍ a in s, f a ∂μ :=
  let ⟨x, hx, h⟩ := nonempty_of_measure_ne_zero (measure_le_set_average_pos hμ hμ₁ hf).ne'
  ⟨x, hx, h⟩
#align measure_theory.exists_le_set_average MeasureTheory.exists_le_set_average

/-- **First moment method**. The maximum of an integrable function is greater than its mean. -/
theorem exists_set_average_le (hμ : μ s ≠ 0) (hμ₁ : μ s ≠ ∞) (hf : IntegrableOn f s μ) :
    ∃ x ∈ s, ⨍ a in s, f a ∂μ ≤ f x :=
  let ⟨x, hx, h⟩ := nonempty_of_measure_ne_zero (measure_set_average_le_pos hμ hμ₁ hf).ne'
  ⟨x, hx, h⟩
#align measure_theory.exists_set_average_le MeasureTheory.exists_set_average_le

section FiniteMeasure

variable [IsFiniteMeasure μ]

/-- **First moment method**. An integrable function is smaller than its mean on a set of positive
measure. -/
theorem measure_le_average_pos (hμ : μ ≠ 0) (hf : Integrable f μ) : 0 < μ {x | f x ≤ ⨍ a, f a ∂μ} :=
  by
  simpa using
    measure_le_set_average_pos (measure.measure_univ_ne_zero.2 hμ) (measure_ne_top _ _)
      hf.integrable_on
#align measure_theory.measure_le_average_pos MeasureTheory.measure_le_average_pos

/-- **First moment method**. An integrable function is greater than its mean on a set of positive
measure. -/
theorem measure_average_le_pos (hμ : μ ≠ 0) (hf : Integrable f μ) : 0 < μ {x | ⨍ a, f a ∂μ ≤ f x} :=
  by
  simpa using
    measure_set_average_le_pos (measure.measure_univ_ne_zero.2 hμ) (measure_ne_top _ _)
      hf.integrable_on
#align measure_theory.measure_average_le_pos MeasureTheory.measure_average_le_pos

/-- **First moment method**. The minimum of an integrable function is smaller than its mean. -/
theorem exists_le_average (hμ : μ ≠ 0) (hf : Integrable f μ) : ∃ x, f x ≤ ⨍ a, f a ∂μ :=
  let ⟨x, hx⟩ := nonempty_of_measure_ne_zero (measure_le_average_pos hμ hf).ne'
  ⟨x, hx⟩
#align measure_theory.exists_le_average MeasureTheory.exists_le_average

/-- **First moment method**. The maximum of an integrable function is greater than its mean. -/
theorem exists_average_le (hμ : μ ≠ 0) (hf : Integrable f μ) : ∃ x, ⨍ a, f a ∂μ ≤ f x :=
  let ⟨x, hx⟩ := nonempty_of_measure_ne_zero (measure_average_le_pos hμ hf).ne'
  ⟨x, hx⟩
#align measure_theory.exists_average_le MeasureTheory.exists_average_le

/- ./././Mathport/Syntax/Translate/Basic.lean:638:2: warning: expanding binder collection (x «expr ∉ » N) -/
/-- **First moment method**. The minimum of an integrable function is smaller than its mean, while
avoiding a null set. -/
theorem exists_not_mem_null_le_average (hμ : μ ≠ 0) (hf : Integrable f μ) (hN : μ N = 0) :
    ∃ (x : _) (_ : x ∉ N), f x ≤ ⨍ a, f a ∂μ :=
  by
  have := measure_le_average_pos hμ hf
  rw [← measure_diff_null hN] at this 
  obtain ⟨x, hx, hxN⟩ := nonempty_of_measure_ne_zero this.ne'
  exact ⟨x, hxN, hx⟩
#align measure_theory.exists_not_mem_null_le_average MeasureTheory.exists_not_mem_null_le_average

/- ./././Mathport/Syntax/Translate/Basic.lean:638:2: warning: expanding binder collection (x «expr ∉ » N) -/
/-- **First moment method**. The maximum of an integrable function is greater than its mean, while
avoiding a null set. -/
theorem exists_not_mem_null_average_le (hμ : μ ≠ 0) (hf : Integrable f μ) (hN : μ N = 0) :
    ∃ (x : _) (_ : x ∉ N), ⨍ a, f a ∂μ ≤ f x := by
  simpa [integral_neg, neg_div] using exists_not_mem_null_le_average hμ hf.neg hN
#align measure_theory.exists_not_mem_null_average_le MeasureTheory.exists_not_mem_null_average_le

end FiniteMeasure

section ProbabilityMeasure

variable [IsProbabilityMeasure μ]

/-- **First moment method**. An integrable function is smaller than its integral on a set of
positive measure. -/
theorem measure_le_integral_pos (hf : Integrable f μ) : 0 < μ {x | f x ≤ ∫ a, f a ∂μ} := by
  simpa only [average_eq_integral] using
    measure_le_average_pos (is_probability_measure.ne_zero μ) hf
#align measure_theory.measure_le_integral_pos MeasureTheory.measure_le_integral_pos

/-- **First moment method**. An integrable function is greater than its integral on a set of
positive measure. -/
theorem measure_integral_le_pos (hf : Integrable f μ) : 0 < μ {x | ∫ a, f a ∂μ ≤ f x} := by
  simpa only [average_eq_integral] using
    measure_average_le_pos (is_probability_measure.ne_zero μ) hf
#align measure_theory.measure_integral_le_pos MeasureTheory.measure_integral_le_pos

/-- **First moment method**. The minimum of an integrable function is smaller than its integral. -/
theorem exists_le_integral (hf : Integrable f μ) : ∃ x, f x ≤ ∫ a, f a ∂μ := by
  simpa only [average_eq_integral] using exists_le_average (is_probability_measure.ne_zero μ) hf
#align measure_theory.exists_le_integral MeasureTheory.exists_le_integral

/-- **First moment method**. The maximum of an integrable function is greater than its integral. -/
theorem exists_integral_le (hf : Integrable f μ) : ∃ x, ∫ a, f a ∂μ ≤ f x := by
  simpa only [average_eq_integral] using exists_average_le (is_probability_measure.ne_zero μ) hf
#align measure_theory.exists_integral_le MeasureTheory.exists_integral_le

/- ./././Mathport/Syntax/Translate/Basic.lean:638:2: warning: expanding binder collection (x «expr ∉ » N) -/
/-- **First moment method**. The minimum of an integrable function is smaller than its integral,
while avoiding a null set. -/
theorem exists_not_mem_null_le_integral (hf : Integrable f μ) (hN : μ N = 0) :
    ∃ (x : _) (_ : x ∉ N), f x ≤ ∫ a, f a ∂μ := by
  simpa only [average_eq_integral] using
    exists_not_mem_null_le_average (is_probability_measure.ne_zero μ) hf hN
#align measure_theory.exists_not_mem_null_le_integral MeasureTheory.exists_not_mem_null_le_integral

/- ./././Mathport/Syntax/Translate/Basic.lean:638:2: warning: expanding binder collection (x «expr ∉ » N) -/
/-- **First moment method**. The maximum of an integrable function is greater than its integral,
while avoiding a null set. -/
theorem exists_not_mem_null_integral_le (hf : Integrable f μ) (hN : μ N = 0) :
    ∃ (x : _) (_ : x ∉ N), ∫ a, f a ∂μ ≤ f x := by
  simpa only [average_eq_integral] using
    exists_not_mem_null_average_le (is_probability_measure.ne_zero μ) hf hN
#align measure_theory.exists_not_mem_null_integral_le MeasureTheory.exists_not_mem_null_integral_le

end ProbabilityMeasure

end FirstMoment

end MeasureTheory

