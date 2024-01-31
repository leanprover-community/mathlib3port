/-
Copyright (c) 2023 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Probability.Kernel.Basic

#align_import probability.kernel.measurable_integral from "leanprover-community/mathlib"@"8af7091a43227e179939ba132e54e54e9f3b089a"

/-!
# Measurability of the integral against a kernel

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

The Lebesgue integral of a measurable function against a kernel is measurable. The Bochner integral
is strongly measurable.

## Main statements

* `measurable.lintegral_kernel_prod_right`: the function `a ↦ ∫⁻ b, f a b ∂(κ a)` is measurable,
  for an s-finite kernel `κ : kernel α β` and a function `f : α → β → ℝ≥0∞` such that `uncurry f`
  is measurable.
* `measure_theory.strongly_measurable.integral_kernel_prod_right`: the function
  `a ↦ ∫ b, f a b ∂(κ a)` is measurable, for an s-finite kernel `κ : kernel α β` and a function
  `f : α → β → E` such that `uncurry f` is measurable.

-/


open MeasureTheory ProbabilityTheory Function Set Filter

open scoped MeasureTheory ENNReal Topology

variable {α β γ : Type _} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {mγ : MeasurableSpace γ}
  {κ : kernel α β} {η : kernel (α × β) γ} {a : α}

namespace ProbabilityTheory

namespace Kernel

#print ProbabilityTheory.kernel.measurable_kernel_prod_mk_left_of_finite /-
/-- This is an auxiliary lemma for `measurable_kernel_prod_mk_left`. -/
theorem measurable_kernel_prod_mk_left_of_finite {t : Set (α × β)} (ht : MeasurableSet t)
    (hκs : ∀ a, IsFiniteMeasure (κ a)) : Measurable fun a => κ a (Prod.mk a ⁻¹' t) :=
  by
  -- `t` is a measurable set in the product `α × β`: we use that the product σ-algebra is generated
  -- by boxes to prove the result by induction.
  refine' MeasurableSpace.induction_on_inter generate_from_prod.symm isPiSystem_prod _ _ _ _ ht
  ·-- case `t = ∅`
    simp only [preimage_empty, measure_empty, measurable_const]
  · -- case of a box: `t = t₁ ×ˢ t₂` for measurable sets `t₁` and `t₂`
    intro t' ht'
    simp only [Set.mem_image2, Set.mem_setOf_eq, exists_and_left] at ht' 
    obtain ⟨t₁, ht₁, t₂, ht₂, rfl⟩ := ht'
    classical
  · -- we assume that the result is true for `t` and we prove it for `tᶜ`
    intro t' ht' h_meas
    have h_eq_sdiff : ∀ a, Prod.mk a ⁻¹' t'ᶜ = Set.univ \ Prod.mk a ⁻¹' t' :=
      by
      intro a
      ext1 b
      simp only [mem_compl_iff, mem_preimage, mem_diff, mem_univ, true_and_iff]
    simp_rw [h_eq_sdiff]
    have :
      (fun a => κ a (Set.univ \ Prod.mk a ⁻¹' t')) = fun a =>
        κ a Set.univ - κ a (Prod.mk a ⁻¹' t') :=
      by
      ext1 a
      rw [← Set.diff_inter_self_eq_diff, Set.inter_univ, measure_diff (Set.subset_univ _)]
      · exact (@measurable_prod_mk_left α β _ _ a) t' ht'
      · exact measure_ne_top _ _
    rw [this]
    exact Measurable.sub (kernel.measurable_coe κ MeasurableSet.univ) h_meas
  · -- we assume that the result is true for a family of disjoint sets and prove it for their union
    intro f h_disj hf_meas hf
    have h_Union :
      (fun a => κ a (Prod.mk a ⁻¹' ⋃ i, f i)) = fun a => κ a (⋃ i, Prod.mk a ⁻¹' f i) :=
      by
      ext1 a
      congr with b
      simp only [mem_Union, mem_preimage]
    rw [h_Union]
    have h_tsum :
      (fun a => κ a (⋃ i, Prod.mk a ⁻¹' f i)) = fun a => ∑' i, κ a (Prod.mk a ⁻¹' f i) :=
      by
      ext1 a
      rw [measure_Union]
      · intro i j hij s hsi hsj b hbs
        have habi : {(a, b)} ⊆ f i := by rw [Set.singleton_subset_iff]; exact hsi hbs
        have habj : {(a, b)} ⊆ f j := by rw [Set.singleton_subset_iff]; exact hsj hbs
        simpa only [Set.bot_eq_empty, Set.le_eq_subset, Set.singleton_subset_iff,
          Set.mem_empty_iff_false] using h_disj hij habi habj
      · exact fun i => (@measurable_prod_mk_left α β _ _ a) _ (hf_meas i)
    rw [h_tsum]
    exact Measurable.ennreal_tsum hf
#align probability_theory.kernel.measurable_kernel_prod_mk_left_of_finite ProbabilityTheory.kernel.measurable_kernel_prod_mk_left_of_finite
-/

#print ProbabilityTheory.kernel.measurable_kernel_prod_mk_left /-
theorem measurable_kernel_prod_mk_left [IsSFiniteKernel κ] {t : Set (α × β)}
    (ht : MeasurableSet t) : Measurable fun a => κ a (Prod.mk a ⁻¹' t) :=
  by
  rw [← kernel_sum_seq κ]
  have : ∀ a, kernel.sum (seq κ) a (Prod.mk a ⁻¹' t) = ∑' n, seq κ n a (Prod.mk a ⁻¹' t) := fun a =>
    kernel.sum_apply' _ _ (measurable_prod_mk_left ht)
  simp_rw [this]
  refine' Measurable.ennreal_tsum fun n => _
  exact measurable_kernel_prod_mk_left_of_finite ht inferInstance
#align probability_theory.kernel.measurable_kernel_prod_mk_left ProbabilityTheory.kernel.measurable_kernel_prod_mk_left
-/

#print ProbabilityTheory.kernel.measurable_kernel_prod_mk_left' /-
theorem measurable_kernel_prod_mk_left' [IsSFiniteKernel η] {s : Set (β × γ)} (hs : MeasurableSet s)
    (a : α) : Measurable fun b => η (a, b) (Prod.mk b ⁻¹' s) :=
  by
  have : ∀ b, Prod.mk b ⁻¹' s = {c | ((a, b), c) ∈ {p : (α × β) × γ | (p.1.2, p.2) ∈ s}} := by
    intro b; rfl
  simp_rw [this]
  refine' (measurable_kernel_prod_mk_left _).comp measurable_prod_mk_left
  exact (measurable_fst.snd.prod_mk measurable_snd) hs
#align probability_theory.kernel.measurable_kernel_prod_mk_left' ProbabilityTheory.kernel.measurable_kernel_prod_mk_left'
-/

#print ProbabilityTheory.kernel.measurable_kernel_prod_mk_right /-
theorem measurable_kernel_prod_mk_right [IsSFiniteKernel κ] {s : Set (β × α)}
    (hs : MeasurableSet s) : Measurable fun y => κ y ((fun x => (x, y)) ⁻¹' s) :=
  measurable_kernel_prod_mk_left (measurableSet_swap_iff.mpr hs)
#align probability_theory.kernel.measurable_kernel_prod_mk_right ProbabilityTheory.kernel.measurable_kernel_prod_mk_right
-/

end Kernel

open ProbabilityTheory.kernel

section Lintegral

variable [IsSFiniteKernel κ] [IsSFiniteKernel η]

#print ProbabilityTheory.kernel.measurable_lintegral_indicator_const /-
/-- Auxiliary lemma for `measurable.lintegral_kernel_prod_right`. -/
theorem kernel.measurable_lintegral_indicator_const {t : Set (α × β)} (ht : MeasurableSet t)
    (c : ℝ≥0∞) : Measurable fun a => ∫⁻ b, t.indicator (Function.const (α × β) c) (a, b) ∂κ a :=
  by
  simp_rw [lintegral_indicator_const_comp measurable_prod_mk_left ht _]
  exact Measurable.const_mul (measurable_kernel_prod_mk_left ht) c
#align probability_theory.kernel.measurable_lintegral_indicator_const ProbabilityTheory.kernel.measurable_lintegral_indicator_const
-/

#print Measurable.lintegral_kernel_prod_right /-
/-- For an s-finite kernel `κ` and a function `f : α → β → ℝ≥0∞` which is measurable when seen as a
map from `α × β` (hypothesis `measurable (uncurry f)`), the integral `a ↦ ∫⁻ b, f a b ∂(κ a)` is
measurable. -/
theorem Measurable.lintegral_kernel_prod_right {f : α → β → ℝ≥0∞} (hf : Measurable (uncurry f)) :
    Measurable fun a => ∫⁻ b, f a b ∂κ a :=
  by
  let F : ℕ → simple_func (α × β) ℝ≥0∞ := simple_func.eapprox (uncurry f)
  have h : ∀ a, (⨆ n, F n a) = uncurry f a := simple_func.supr_eapprox_apply (uncurry f) hf
  simp only [Prod.forall, uncurry_apply_pair] at h 
  simp_rw [← h]
  have : ∀ a, ∫⁻ b, ⨆ n, F n (a, b) ∂κ a = ⨆ n, ∫⁻ b, F n (a, b) ∂κ a :=
    by
    intro a
    rw [lintegral_supr]
    · exact fun n => (F n).Measurable.comp measurable_prod_mk_left
    · exact fun i j hij b => simple_func.monotone_eapprox (uncurry f) hij _
  simp_rw [this]
  refine' measurable_iSup fun n => simple_func.induction _ _ (F n)
  · intro c t ht
    simp only [simple_func.const_zero, simple_func.coe_piecewise, simple_func.coe_const,
      simple_func.coe_zero, Set.piecewise_eq_indicator]
    exact kernel.measurable_lintegral_indicator_const ht c
  · intro g₁ g₂ h_disj hm₁ hm₂
    simp only [simple_func.coe_add, Pi.add_apply]
    have h_add :
      (fun a => ∫⁻ b, g₁ (a, b) + g₂ (a, b) ∂κ a) =
        (fun a => ∫⁻ b, g₁ (a, b) ∂κ a) + fun a => ∫⁻ b, g₂ (a, b) ∂κ a :=
      by
      ext1 a
      rw [Pi.add_apply, lintegral_add_left (g₁.measurable.comp measurable_prod_mk_left)]
    rw [h_add]
    exact Measurable.add hm₁ hm₂
#align measurable.lintegral_kernel_prod_right Measurable.lintegral_kernel_prod_right
-/

#print Measurable.lintegral_kernel_prod_right' /-
theorem Measurable.lintegral_kernel_prod_right' {f : α × β → ℝ≥0∞} (hf : Measurable f) :
    Measurable fun a => ∫⁻ b, f (a, b) ∂κ a :=
  by
  refine' Measurable.lintegral_kernel_prod_right _
  have : (uncurry fun (a : α) (b : β) => f (a, b)) = f := by ext x;
    rw [← @Prod.mk.eta _ _ x, uncurry_apply_pair]
  rwa [this]
#align measurable.lintegral_kernel_prod_right' Measurable.lintegral_kernel_prod_right'
-/

#print Measurable.lintegral_kernel_prod_right'' /-
theorem Measurable.lintegral_kernel_prod_right'' {f : β × γ → ℝ≥0∞} (hf : Measurable f) :
    Measurable fun x => ∫⁻ y, f (x, y) ∂η (a, x) :=
  by
  change
    Measurable
      ((fun x => ∫⁻ y, (fun u : (α × β) × γ => f (u.1.2, u.2)) (x, y) ∂η x) ∘ fun x => (a, x))
  refine' (Measurable.lintegral_kernel_prod_right' _).comp measurable_prod_mk_left
  exact hf.comp (measurable_fst.snd.prod_mk measurable_snd)
#align measurable.lintegral_kernel_prod_right'' Measurable.lintegral_kernel_prod_right''
-/

#print Measurable.set_lintegral_kernel_prod_right /-
theorem Measurable.set_lintegral_kernel_prod_right {f : α → β → ℝ≥0∞} (hf : Measurable (uncurry f))
    {s : Set β} (hs : MeasurableSet s) : Measurable fun a => ∫⁻ b in s, f a b ∂κ a := by
  simp_rw [← lintegral_restrict κ hs]; exact hf.lintegral_kernel_prod_right
#align measurable.set_lintegral_kernel_prod_right Measurable.set_lintegral_kernel_prod_right
-/

#print Measurable.lintegral_kernel_prod_left' /-
theorem Measurable.lintegral_kernel_prod_left' {f : β × α → ℝ≥0∞} (hf : Measurable f) :
    Measurable fun y => ∫⁻ x, f (x, y) ∂κ y :=
  (measurable_swap_iff.mpr hf).lintegral_kernel_prod_right'
#align measurable.lintegral_kernel_prod_left' Measurable.lintegral_kernel_prod_left'
-/

#print Measurable.lintegral_kernel_prod_left /-
theorem Measurable.lintegral_kernel_prod_left {f : β → α → ℝ≥0∞} (hf : Measurable (uncurry f)) :
    Measurable fun y => ∫⁻ x, f x y ∂κ y :=
  hf.lintegral_kernel_prod_left'
#align measurable.lintegral_kernel_prod_left Measurable.lintegral_kernel_prod_left
-/

#print Measurable.set_lintegral_kernel_prod_left /-
theorem Measurable.set_lintegral_kernel_prod_left {f : β → α → ℝ≥0∞} (hf : Measurable (uncurry f))
    {s : Set β} (hs : MeasurableSet s) : Measurable fun b => ∫⁻ a in s, f a b ∂κ b := by
  simp_rw [← lintegral_restrict κ hs]; exact hf.lintegral_kernel_prod_left
#align measurable.set_lintegral_kernel_prod_left Measurable.set_lintegral_kernel_prod_left
-/

#print Measurable.lintegral_kernel /-
theorem Measurable.lintegral_kernel {f : β → ℝ≥0∞} (hf : Measurable f) :
    Measurable fun a => ∫⁻ b, f b ∂κ a :=
  Measurable.lintegral_kernel_prod_right (hf.comp measurable_snd)
#align measurable.lintegral_kernel Measurable.lintegral_kernel
-/

#print Measurable.set_lintegral_kernel /-
theorem Measurable.set_lintegral_kernel {f : β → ℝ≥0∞} (hf : Measurable f) {s : Set β}
    (hs : MeasurableSet s) : Measurable fun a => ∫⁻ b in s, f b ∂κ a :=
  Measurable.set_lintegral_kernel_prod_right (hf.comp measurable_snd) hs
#align measurable.set_lintegral_kernel Measurable.set_lintegral_kernel
-/

end Lintegral

variable {E : Type _} [NormedAddCommGroup E] [IsSFiniteKernel κ] [IsSFiniteKernel η]

#print ProbabilityTheory.measurableSet_kernel_integrable /-
theorem measurableSet_kernel_integrable ⦃f : α → β → E⦄ (hf : StronglyMeasurable (uncurry f)) :
    MeasurableSet {x | Integrable (f x) (κ x)} :=
  by
  simp_rw [integrable, hf.of_uncurry_left.ae_strongly_measurable, true_and_iff]
  exact measurableSet_lt (Measurable.lintegral_kernel_prod_right hf.ennnorm) measurable_const
#align probability_theory.measurable_set_kernel_integrable ProbabilityTheory.measurableSet_kernel_integrable
-/

end ProbabilityTheory

open ProbabilityTheory ProbabilityTheory.kernel

namespace MeasureTheory

variable {E : Type _} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [IsSFiniteKernel κ]
  [IsSFiniteKernel η]

#print MeasureTheory.StronglyMeasurable.integral_kernel_prod_right /-
theorem StronglyMeasurable.integral_kernel_prod_right ⦃f : α → β → E⦄
    (hf : StronglyMeasurable (uncurry f)) : StronglyMeasurable fun x => ∫ y, f x y ∂κ x := by
  classical
#align measure_theory.strongly_measurable.integral_kernel_prod_right MeasureTheory.StronglyMeasurable.integral_kernel_prod_right
-/

#print MeasureTheory.StronglyMeasurable.integral_kernel_prod_right' /-
theorem StronglyMeasurable.integral_kernel_prod_right' ⦃f : α × β → E⦄ (hf : StronglyMeasurable f) :
    StronglyMeasurable fun x => ∫ y, f (x, y) ∂κ x := by rw [← uncurry_curry f] at hf ;
  exact hf.integral_kernel_prod_right
#align measure_theory.strongly_measurable.integral_kernel_prod_right' MeasureTheory.StronglyMeasurable.integral_kernel_prod_right'
-/

#print MeasureTheory.StronglyMeasurable.integral_kernel_prod_right'' /-
theorem StronglyMeasurable.integral_kernel_prod_right'' {f : β × γ → E}
    (hf : StronglyMeasurable f) : StronglyMeasurable fun x => ∫ y, f (x, y) ∂η (a, x) :=
  by
  change
    strongly_measurable
      ((fun x => ∫ y, (fun u : (α × β) × γ => f (u.1.2, u.2)) (x, y) ∂η x) ∘ fun x => (a, x))
  refine' strongly_measurable.comp_measurable _ measurable_prod_mk_left
  refine' MeasureTheory.StronglyMeasurable.integral_kernel_prod_right' _
  exact hf.comp_measurable (measurable_fst.snd.prod_mk measurable_snd)
#align measure_theory.strongly_measurable.integral_kernel_prod_right'' MeasureTheory.StronglyMeasurable.integral_kernel_prod_right''
-/

#print MeasureTheory.StronglyMeasurable.integral_kernel_prod_left /-
theorem StronglyMeasurable.integral_kernel_prod_left ⦃f : β → α → E⦄
    (hf : StronglyMeasurable (uncurry f)) : StronglyMeasurable fun y => ∫ x, f x y ∂κ y :=
  (hf.comp_measurable measurable_swap).integral_kernel_prod_right'
#align measure_theory.strongly_measurable.integral_kernel_prod_left MeasureTheory.StronglyMeasurable.integral_kernel_prod_left
-/

#print MeasureTheory.StronglyMeasurable.integral_kernel_prod_left' /-
theorem StronglyMeasurable.integral_kernel_prod_left' ⦃f : β × α → E⦄ (hf : StronglyMeasurable f) :
    StronglyMeasurable fun y => ∫ x, f (x, y) ∂κ y :=
  (hf.comp_measurable measurable_swap).integral_kernel_prod_right'
#align measure_theory.strongly_measurable.integral_kernel_prod_left' MeasureTheory.StronglyMeasurable.integral_kernel_prod_left'
-/

#print MeasureTheory.StronglyMeasurable.integral_kernel_prod_left'' /-
theorem StronglyMeasurable.integral_kernel_prod_left'' {f : γ × β → E} (hf : StronglyMeasurable f) :
    StronglyMeasurable fun y => ∫ x, f (x, y) ∂η (a, y) :=
  by
  change
    strongly_measurable
      ((fun y => ∫ x, (fun u : γ × α × β => f (u.1, u.2.2)) (x, y) ∂η y) ∘ fun x => (a, x))
  refine' strongly_measurable.comp_measurable _ measurable_prod_mk_left
  refine' MeasureTheory.StronglyMeasurable.integral_kernel_prod_left' _
  exact hf.comp_measurable (measurable_fst.prod_mk measurable_snd.snd)
#align measure_theory.strongly_measurable.integral_kernel_prod_left'' MeasureTheory.StronglyMeasurable.integral_kernel_prod_left''
-/

end MeasureTheory

