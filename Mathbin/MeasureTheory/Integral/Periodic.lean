/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Alex Kontorovich, Heather Macbeth
-/
import Mathbin.MeasureTheory.Measure.HaarQuotient
import Mathbin.MeasureTheory.Integral.IntervalIntegral
import Mathbin.Topology.Algebra.Order.Floor

/-!
# Integrals of periodic functions

In this file we prove that the half-open interval `Ioc t (t + T)` in `ℝ` is a fundamental domain of
the action of the subgroup `ℤ ∙ T` on `ℝ`.

A consequence is `add_circle.measure_preserving_mk`: the covering map from `ℝ` to the "additive
circle" `ℝ ⧸ (ℤ ∙ T)` is measure-preserving, with respect to the restriction of Lebesgue measure to
`Ioc t (t + T)` (upstairs) and with respect to Haar measure (downstairs).

Another consequence (`function.periodic.interval_integral_add_eq` and related declarations) is that
`∫ x in t..t + T, f x = ∫ x in s..s + T, f x` for any (not necessarily measurable) function with
period `T`.
-/


open Set Function MeasureTheory MeasureTheory.Measure TopologicalSpace AddSubgroup intervalIntegral

open MeasureTheory Nnreal Ennreal

attribute [-instance] QuotientAddGroup.measurableSpace Quotient.measurableSpace

theorem isAddFundamentalDomainIoc {T : ℝ} (hT : 0 < T) (t : ℝ)
    (μ : Measure ℝ := by exact MeasureTheory.MeasureSpace.volume) :
    IsAddFundamentalDomain (AddSubgroup.zmultiples T) (ioc t (t + T)) μ := by
  refine' is_add_fundamental_domain.mk' measurable_set_Ioc.null_measurable_set fun x => _
  have : bijective (cod_restrict (fun n : ℤ => n • T) (AddSubgroup.zmultiples T) _) :=
    (Equiv.ofInjective (fun n : ℤ => n • T) (zsmul_strict_mono_left hT).Injective).Bijective
  refine' this.exists_unique_iff.2 _
  simpa only [add_comm x] using exists_unique_add_zsmul_mem_Ioc hT x t
#align is_add_fundamental_domain_Ioc isAddFundamentalDomainIoc

theorem isAddFundamentalDomainIoc' {T : ℝ} (hT : 0 < T) (t : ℝ)
    (μ : Measure ℝ := by exact MeasureTheory.MeasureSpace.volume) :
    IsAddFundamentalDomain (AddSubgroup.zmultiples T).opposite (ioc t (t + T)) μ := by
  refine' is_add_fundamental_domain.mk' measurable_set_Ioc.null_measurable_set fun x => _
  have : bijective (cod_restrict (fun n : ℤ => n • T) (AddSubgroup.zmultiples T) _) :=
    (Equiv.ofInjective (fun n : ℤ => n • T) (zsmul_strict_mono_left hT).Injective).Bijective
  refine' this.exists_unique_iff.2 _
  simpa using exists_unique_add_zsmul_mem_Ioc hT x t
#align is_add_fundamental_domain_Ioc' isAddFundamentalDomainIoc'

namespace AddCircle

variable (T : ℝ) [hT : Fact (0 < T)]

include hT

/-- Equip the "additive circle" `ℝ ⧸ (ℤ ∙ T)` with, as a standard measure, the Haar measure of total
mass `T` -/
noncomputable instance measureSpace : MeasureSpace (AddCircle T) :=
  { AddCircle.measurableSpace with volume := Ennreal.ofReal T • addHaarMeasure ⊤ }
#align add_circle.measure_space AddCircle.measureSpace

@[simp]
protected theorem measure_univ : volume (Set.univ : Set (AddCircle T)) = Ennreal.ofReal T := by
  dsimp [volume]
  rw [← positive_compacts.coe_top]
  simp [add_haar_measure_self, -positive_compacts.coe_top]
#align add_circle.measure_univ AddCircle.measure_univ

instance : IsAddHaarMeasure (volume : Measure (AddCircle T)) :=
  IsAddHaarMeasure.smul _ (by simp [hT.out]) Ennreal.of_real_ne_top

instance isFiniteMeasure :
    IsFiniteMeasure (volume : Measure (AddCircle T)) where measure_univ_lt_top := by simp
#align add_circle.is_finite_measure AddCircle.isFiniteMeasure

/-- The covering map from `ℝ` to the "additive circle" `ℝ ⧸ (ℤ ∙ T)` is measure-preserving,
considered with respect to the standard measure (defined to be the Haar measure of total mass `T`)
on the additive circle, and with respect to the restriction of Lebsegue measure on `ℝ` to an
interval (t, t + T]. -/
protected theorem measurePreservingMk (t : ℝ) :
    MeasurePreserving (coe : ℝ → AddCircle T) (volume.restrict (ioc t (t + T))) :=
  MeasurePreservingQuotientAddGroup.mk' (isAddFundamentalDomainIoc' hT.out t)
    (⊤ : PositiveCompacts (AddCircle T)) (by simp) T.toNnreal
    (by simp [← Ennreal.of_real_coe_nnreal, Real.coe_to_nnreal T hT.out.le])
#align add_circle.measure_preserving_mk AddCircle.measurePreservingMk

theorem volume_closed_ball {x : AddCircle T} (ε : ℝ) :
    volume (Metric.closedBall x ε) = Ennreal.ofReal (min T (2 * ε)) := by
  have hT' : |T| = T := abs_eq_self.mpr hT.out.le
  let I := Ioc (-(T / 2)) (T / 2)
  have h₁ : ε < T / 2 → Metric.closedBall (0 : ℝ) ε ∩ I = Metric.closedBall (0 : ℝ) ε := by
    intro hε
    rw [inter_eq_left_iff_subset, Real.closed_ball_eq_Icc, zero_sub, zero_add]
    rintro y ⟨hy₁, hy₂⟩
    constructor <;> linarith
  have h₂ :
    coe ⁻¹' Metric.closedBall (0 : AddCircle T) ε ∩ I =
      if ε < T / 2 then Metric.closedBall (0 : ℝ) ε else I :=
    by 
    conv_rhs => rw [← if_ctx_congr (Iff.rfl : ε < T / 2 ↔ ε < T / 2) h₁ fun _ => rfl, ← hT']
    apply coe_real_preimage_closed_ball_inter_eq
    simpa only [hT', Real.closed_ball_eq_Icc, zero_add, zero_sub] using Ioc_subset_Icc_self
  rw [add_haar_closed_ball_center]
  simp only [restrict_apply' measurableSetIoc, (by linarith : -(T / 2) + T = T / 2), h₂, ←
    (AddCircle.measurePreservingMk T (-(T / 2))).measure_preimage measurableSetClosedBall]
  by_cases hε : ε < T / 2
  · simp [hε, min_eq_right (by linarith : 2 * ε ≤ T)]
  · simp [hε, min_eq_left (by linarith : T ≤ 2 * ε)]
#align add_circle.volume_closed_ball AddCircle.volume_closed_ball

instance : IsDoublingMeasure (volume : Measure (AddCircle T)) := by
  refine' ⟨⟨Real.toNnreal 2, Filter.eventually_of_forall fun ε x => _⟩⟩
  simp only [volume_closed_ball]
  erw [← Ennreal.of_real_mul zero_le_two]
  apply Ennreal.of_real_le_of_real
  rw [mul_min_of_nonneg _ _ (zero_le_two : (0 : ℝ) ≤ 2)]
  exact min_le_min (by linarith [hT.out]) (le_refl _)

/-- The integral of a measurable function over `add_circle T` is equal to the integral over an
interval (t, t + T] in `ℝ` of its lift to `ℝ`. -/
protected theorem lintegral_preimage (t : ℝ) {f : AddCircle T → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ a in ioc t (t + T), f a) = ∫⁻ b : AddCircle T, f b := by
  rw [← lintegral_map hf AddCircle.measurableMk', (AddCircle.measurePreservingMk T t).map_eq]
#align add_circle.lintegral_preimage AddCircle.lintegral_preimage

variable {E : Type _} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- The integral of an almost-everywhere strongly measurable function over `add_circle T` is equal
to the integral over an interval (t, t + T] in `ℝ` of its lift to `ℝ`. -/
protected theorem integral_preimage (t : ℝ) {f : AddCircle T → E}
    (hf : AeStronglyMeasurable f volume) : (∫ a in ioc t (t + T), f a) = ∫ b : AddCircle T, f b :=
  by 
  rw [← (AddCircle.measurePreservingMk T t).map_eq] at hf⊢
  rw [integral_map add_circle.measurable_mk'.ae_measurable hf]
#align add_circle.integral_preimage AddCircle.integral_preimage

/-- The integral of an almost-everywhere strongly measurable function over `add_circle T` is equal
to the integral over an interval (t, t + T] in `ℝ` of its lift to `ℝ`. -/
protected theorem interval_integral_preimage (t : ℝ) {f : AddCircle T → E}
    (hf : AeStronglyMeasurable f volume) : (∫ a in t..t + T, f a) = ∫ b : AddCircle T, f b := by
  rw [integral_of_le, AddCircle.integral_preimage T t hf]
  linarith [hT.out]
#align add_circle.interval_integral_preimage AddCircle.interval_integral_preimage

end AddCircle

namespace UnitAddCircle

private theorem fact_zero_lt_one : Fact ((0 : ℝ) < 1) :=
  ⟨zero_lt_one⟩
#align unit_add_circle.fact_zero_lt_one unit_add_circle.fact_zero_lt_one

attribute [local instance] fact_zero_lt_one

noncomputable instance measureSpace : MeasureSpace UnitAddCircle :=
  AddCircle.measureSpace 1
#align unit_add_circle.measure_space UnitAddCircle.measureSpace

@[simp]
protected theorem measure_univ : volume (Set.univ : Set UnitAddCircle) = 1 := by simp
#align unit_add_circle.measure_univ UnitAddCircle.measure_univ

instance isFiniteMeasure : IsFiniteMeasure (volume : Measure UnitAddCircle) :=
  AddCircle.isFiniteMeasure 1
#align unit_add_circle.is_finite_measure UnitAddCircle.isFiniteMeasure

/-- The covering map from `ℝ` to the "unit additive circle" `ℝ ⧸ ℤ` is measure-preserving,
considered with respect to the standard measure (defined to be the Haar measure of total mass 1)
on the additive circle, and with respect to the restriction of Lebsegue measure on `ℝ` to an
interval (t, t + 1]. -/
protected theorem measurePreservingMk (t : ℝ) :
    MeasurePreserving (coe : ℝ → UnitAddCircle) (volume.restrict (ioc t (t + 1))) :=
  AddCircle.measurePreservingMk 1 t
#align unit_add_circle.measure_preserving_mk UnitAddCircle.measurePreservingMk

/-- The integral of a measurable function over `unit_add_circle` is equal to the integral over an
interval (t, t + 1] in `ℝ` of its lift to `ℝ`. -/
protected theorem lintegral_preimage (t : ℝ) {f : UnitAddCircle → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ a in ioc t (t + 1), f a) = ∫⁻ b : UnitAddCircle, f b :=
  AddCircle.lintegral_preimage 1 t hf
#align unit_add_circle.lintegral_preimage UnitAddCircle.lintegral_preimage

variable {E : Type _} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- The integral of an almost-everywhere strongly measurable function over `unit_add_circle` is
equal to the integral over an interval (t, t + 1] in `ℝ` of its lift to `ℝ`. -/
protected theorem integral_preimage (t : ℝ) {f : UnitAddCircle → E}
    (hf : AeStronglyMeasurable f volume) : (∫ a in ioc t (t + 1), f a) = ∫ b : UnitAddCircle, f b :=
  AddCircle.integral_preimage 1 t hf
#align unit_add_circle.integral_preimage UnitAddCircle.integral_preimage

/-- The integral of an almost-everywhere strongly measurable function over `unit_add_circle` is
equal to the integral over an interval (t, t + 1] in `ℝ` of its lift to `ℝ`. -/
protected theorem interval_integral_preimage (t : ℝ) {f : UnitAddCircle → E}
    (hf : AeStronglyMeasurable f volume) : (∫ a in t..t + 1, f a) = ∫ b : UnitAddCircle, f b :=
  AddCircle.interval_integral_preimage 1 t hf
#align unit_add_circle.interval_integral_preimage UnitAddCircle.interval_integral_preimage

end UnitAddCircle

variable {E : Type _} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

namespace Function

namespace Periodic

variable {f : ℝ → E} {T : ℝ}

/-- An auxiliary lemma for a more general `function.periodic.interval_integral_add_eq`. -/
theorem interval_integral_add_eq_of_pos (hf : Periodic f T) (hT : 0 < T) (t s : ℝ) :
    (∫ x in t..t + T, f x) = ∫ x in s..s + T, f x := by
  simp only [integral_of_le, hT.le, le_add_iff_nonneg_right]
  haveI : vadd_invariant_measure (AddSubgroup.zmultiples T) ℝ volume :=
    ⟨fun c s hs => measure_preimage_add _ _ _⟩
  exact
    (isAddFundamentalDomainIoc hT t).set_integral_eq (isAddFundamentalDomainIoc hT s)
      hf.map_vadd_zmultiples
#align
  function.periodic.interval_integral_add_eq_of_pos Function.Periodic.interval_integral_add_eq_of_pos

/-- If `f` is a periodic function with period `T`, then its integral over `[t, t + T]` does not
depend on `t`. -/
theorem interval_integral_add_eq (hf : Periodic f T) (t s : ℝ) :
    (∫ x in t..t + T, f x) = ∫ x in s..s + T, f x := by
  rcases lt_trichotomy 0 T with (hT | rfl | hT)
  · exact hf.interval_integral_add_eq_of_pos hT t s
  · simp
  · rw [← neg_inj, ← integral_symm, ← integral_symm]
    simpa only [← sub_eq_add_neg, add_sub_cancel] using
      hf.neg.interval_integral_add_eq_of_pos (neg_pos.2 hT) (t + T) (s + T)
#align function.periodic.interval_integral_add_eq Function.Periodic.interval_integral_add_eq

/-- If `f` is an integrable periodic function with period `T`, then its integral over `[t, s + T]`
is the sum of its integrals over the intervals `[t, s]` and `[t, t + T]`. -/
theorem interval_integral_add_eq_add (hf : Periodic f T) (t s : ℝ)
    (h_int : ∀ t₁ t₂, IntervalIntegrable f MeasureSpace.volume t₁ t₂) :
    (∫ x in t..s + T, f x) = (∫ x in t..s, f x) + ∫ x in t..t + T, f x := by
  rw [hf.interval_integral_add_eq t s, integral_add_adjacent_intervals (h_int t s) (h_int s _)]
#align function.periodic.interval_integral_add_eq_add Function.Periodic.interval_integral_add_eq_add

/-- If `f` is an integrable periodic function with period `T`, and `n` is an integer, then its
integral over `[t, t + n • T]` is `n` times its integral over `[t, t + T]`. -/
theorem interval_integral_add_zsmul_eq (hf : Periodic f T) (n : ℤ) (t : ℝ)
    (h_int : ∀ t₁ t₂, IntervalIntegrable f MeasureSpace.volume t₁ t₂) :
    (∫ x in t..t + n • T, f x) = n • ∫ x in t..t + T, f x :=
  by
  -- Reduce to the case `b = 0`
  suffices (∫ x in 0 ..n • T, f x) = n • ∫ x in 0 ..T, f x by
    simp only [hf.interval_integral_add_eq t 0, (hf.zsmul n).interval_integral_add_eq t 0, zero_add,
      this]
  -- First prove it for natural numbers
  have : ∀ m : ℕ, (∫ x in 0 ..m • T, f x) = m • ∫ x in 0 ..T, f x := by
    intros
    induction' m with m ih
    · simp
    · simp only [succ_nsmul', hf.interval_integral_add_eq_add 0 (m • T) h_int, ih, zero_add]
  -- Then prove it for all integers
  cases' n with n n
  · simp [← this n]
  · conv_rhs => rw [zsmul_neg_succ_of_nat]
    have h₀ : Int.negSucc n • T + (n + 1) • T = 0 := by
      simp
      linarith
    rw [integral_symm, ← (hf.nsmul (n + 1)).funext, neg_inj]
    simp_rw [integral_comp_add_right, h₀, zero_add, this (n + 1), add_comm T,
      hf.interval_integral_add_eq ((n + 1) • T) 0, zero_add]
#align
  function.periodic.interval_integral_add_zsmul_eq Function.Periodic.interval_integral_add_zsmul_eq

section RealValued

open Filter

variable {g : ℝ → ℝ}

variable (hg : Periodic g T) (h_int : ∀ t₁ t₂, IntervalIntegrable g MeasureSpace.volume t₁ t₂)

include hg h_int

/-- If `g : ℝ → ℝ` is periodic with period `T > 0`, then for any `t : ℝ`, the function
`t ↦ ∫ x in 0..t, g x` is bounded below by `t ↦ X + ⌊t/T⌋ • Y` for appropriate constants `X` and
`Y`. -/
theorem Inf_add_zsmul_le_integral_of_pos (hT : 0 < T) (t : ℝ) :
    (inf ((fun t => ∫ x in 0 ..t, g x) '' icc 0 T) + ⌊t / T⌋ • ∫ x in 0 ..T, g x) ≤
      ∫ x in 0 ..t, g x :=
  by 
  let ε := Int.fract (t / T) * T
  conv_rhs =>
    rw [← Int.fract_div_mul_self_add_zsmul_eq T t (by linarith), ←
      integral_add_adjacent_intervals (h_int 0 ε) (h_int _ _)]
  rw [hg.interval_integral_add_zsmul_eq ⌊t / T⌋ ε h_int, hg.interval_integral_add_eq ε 0, zero_add,
    add_le_add_iff_right]
  exact
    (continuous_primitive h_int 0).ContinuousOn.Inf_image_Icc_le
      (mem_Icc_of_Ico (Int.fract_div_mul_self_mem_Ico T t hT))
#align
  function.periodic.Inf_add_zsmul_le_integral_of_pos Function.Periodic.Inf_add_zsmul_le_integral_of_pos

/-- If `g : ℝ → ℝ` is periodic with period `T > 0`, then for any `t : ℝ`, the function
`t ↦ ∫ x in 0..t, g x` is bounded above by `t ↦ X + ⌊t/T⌋ • Y` for appropriate constants `X` and
`Y`. -/
theorem integral_le_Sup_add_zsmul_of_pos (hT : 0 < T) (t : ℝ) :
    (∫ x in 0 ..t, g x) ≤
      sup ((fun t => ∫ x in 0 ..t, g x) '' icc 0 T) + ⌊t / T⌋ • ∫ x in 0 ..T, g x :=
  by 
  let ε := Int.fract (t / T) * T
  conv_lhs =>
    rw [← Int.fract_div_mul_self_add_zsmul_eq T t (by linarith), ←
      integral_add_adjacent_intervals (h_int 0 ε) (h_int _ _)]
  rw [hg.interval_integral_add_zsmul_eq ⌊t / T⌋ ε h_int, hg.interval_integral_add_eq ε 0, zero_add,
    add_le_add_iff_right]
  exact
    (continuous_primitive h_int 0).ContinuousOn.le_Sup_image_Icc
      (mem_Icc_of_Ico (Int.fract_div_mul_self_mem_Ico T t hT))
#align
  function.periodic.integral_le_Sup_add_zsmul_of_pos Function.Periodic.integral_le_Sup_add_zsmul_of_pos

/-- If `g : ℝ → ℝ` is periodic with period `T > 0` and `0 < ∫ x in 0..T, g x`, then
`t ↦ ∫ x in 0..t, g x` tends to `∞` as `t` tends to `∞`. -/
theorem tendsto_at_top_interval_integral_of_pos (h₀ : 0 < ∫ x in 0 ..T, g x) (hT : 0 < T) :
    Tendsto (fun t => ∫ x in 0 ..t, g x) atTop atTop := by
  apply tendsto_at_top_mono (hg.Inf_add_zsmul_le_integral_of_pos h_int hT)
  apply at_top.tendsto_at_top_add_const_left (Inf <| (fun t => ∫ x in 0 ..t, g x) '' Icc 0 T)
  apply tendsto.at_top_zsmul_const h₀
  exact tendsto_floor_at_top.comp (tendsto_id.at_top_mul_const (inv_pos.mpr hT))
#align
  function.periodic.tendsto_at_top_interval_integral_of_pos Function.Periodic.tendsto_at_top_interval_integral_of_pos

/-- If `g : ℝ → ℝ` is periodic with period `T > 0` and `0 < ∫ x in 0..T, g x`, then
`t ↦ ∫ x in 0..t, g x` tends to `-∞` as `t` tends to `-∞`. -/
theorem tendsto_at_bot_interval_integral_of_pos (h₀ : 0 < ∫ x in 0 ..T, g x) (hT : 0 < T) :
    Tendsto (fun t => ∫ x in 0 ..t, g x) atBot atBot := by
  apply tendsto_at_bot_mono (hg.integral_le_Sup_add_zsmul_of_pos h_int hT)
  apply at_bot.tendsto_at_bot_add_const_left (Sup <| (fun t => ∫ x in 0 ..t, g x) '' Icc 0 T)
  apply tendsto.at_bot_zsmul_const h₀
  exact tendsto_floor_at_bot.comp (tendsto_id.at_bot_mul_const (inv_pos.mpr hT))
#align
  function.periodic.tendsto_at_bot_interval_integral_of_pos Function.Periodic.tendsto_at_bot_interval_integral_of_pos

/-- If `g : ℝ → ℝ` is periodic with period `T > 0` and `∀ x, 0 < g x`, then `t ↦ ∫ x in 0..t, g x`
tends to `∞` as `t` tends to `∞`. -/
theorem tendsto_at_top_interval_integral_of_pos' (h₀ : ∀ x, 0 < g x) (hT : 0 < T) :
    Tendsto (fun t => ∫ x in 0 ..t, g x) atTop atTop :=
  hg.tendsto_at_top_interval_integral_of_pos h_int (interval_integral_pos_of_pos (h_int 0 T) h₀ hT)
    hT
#align
  function.periodic.tendsto_at_top_interval_integral_of_pos' Function.Periodic.tendsto_at_top_interval_integral_of_pos'

/-- If `g : ℝ → ℝ` is periodic with period `T > 0` and `∀ x, 0 < g x`, then `t ↦ ∫ x in 0..t, g x`
tends to `-∞` as `t` tends to `-∞`. -/
theorem tendsto_at_bot_interval_integral_of_pos' (h₀ : ∀ x, 0 < g x) (hT : 0 < T) :
    Tendsto (fun t => ∫ x in 0 ..t, g x) atBot atBot :=
  hg.tendsto_at_bot_interval_integral_of_pos h_int (interval_integral_pos_of_pos (h_int 0 T) h₀ hT)
    hT
#align
  function.periodic.tendsto_at_bot_interval_integral_of_pos' Function.Periodic.tendsto_at_bot_interval_integral_of_pos'

end RealValued

end Periodic

end Function

