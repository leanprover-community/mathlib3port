/-
Copyright (c) 2023 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne

! This file was ported from Lean 3 source module probability.kernel.measurable_integral
! leanprover-community/mathlib commit 483dd86cfec4a1380d22b1f6acd4c3dc53f501ff
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Probability.Kernel.Basic

/-!
# Measurability of the integral against a kernel

The Lebesgue integral of a measurable function against a kernel is measurable.

## Main statements

* `probability_theory.kernel.measurable_lintegral`: the function `a ↦ ∫⁻ b, f a b ∂(κ a)` is
  measurable, for an s-finite kernel `κ : kernel α β` and a function `f : α → β → ℝ≥0∞` such that
  `function.uncurry f` is measurable.


-/


open MeasureTheory ProbabilityTheory

open MeasureTheory ENNReal NNReal BigOperators

namespace ProbabilityTheory.kernel

variable {α β ι : Type _} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}

include mα mβ

/-- This is an auxiliary lemma for `measurable_prod_mk_mem`. -/
theorem measurable_prod_mk_mem_of_finite (κ : kernel α β) {t : Set (α × β)} (ht : MeasurableSet t)
    (hκs : ∀ a, IsFiniteMeasure (κ a)) : Measurable fun a => κ a { b | (a, b) ∈ t } :=
  by
  -- `t` is a measurable set in the product `α × β`: we use that the product σ-algebra is generated
  -- by boxes to prove the result by induction.
  refine' MeasurableSpace.induction_on_inter generate_from_prod.symm isPiSystem_prod _ _ _ _ ht
  ·-- case `t = ∅`
    simp only [Set.mem_empty_iff_false, Set.setOf_false, measure_empty, measurable_const]
  · -- case of a box: `t = t₁ ×ˢ t₂` for measurable sets `t₁` and `t₂`
    intro t' ht'
    simp only [Set.mem_image2, Set.mem_setOf_eq, exists_and_left] at ht'
    obtain ⟨t₁, ht₁, t₂, ht₂, rfl⟩ := ht'
    simp only [Set.prod_mk_mem_set_prod_eq]
    classical
      have h_eq_ite :
        (fun a => κ a { b : β | a ∈ t₁ ∧ b ∈ t₂ }) = fun a => ite (a ∈ t₁) (κ a t₂) 0 :=
        by
        ext1 a
        split_ifs
        · simp only [h, true_and_iff]
          rfl
        · simp only [h, false_and_iff, Set.setOf_false, Set.inter_empty, measure_empty]
      rw [h_eq_ite]
      exact Measurable.ite ht₁ (kernel.measurable_coe κ ht₂) measurable_const
  · -- we assume that the result is true for `t` and we prove it for `tᶜ`
    intro t' ht' h_meas
    have h_eq_sdiff : ∀ a, { b : β | (a, b) ∈ t'ᶜ } = Set.univ \ { b : β | (a, b) ∈ t' } :=
      by
      intro a
      ext1 b
      simp only [Set.mem_compl_iff, Set.mem_setOf_eq, Set.mem_diff, Set.mem_univ, true_and_iff]
    simp_rw [h_eq_sdiff]
    have :
      (fun a => κ a (Set.univ \ { b : β | (a, b) ∈ t' })) = fun a =>
        κ a Set.univ - κ a { b : β | (a, b) ∈ t' } :=
      by
      ext1 a
      rw [← Set.diff_inter_self_eq_diff, Set.inter_univ, measure_diff]
      · exact Set.subset_univ _
      · exact (@measurable_prod_mk_left α β _ _ a) t' ht'
      · exact measure_ne_top _ _
    rw [this]
    exact Measurable.sub (kernel.measurable_coe κ MeasurableSet.univ) h_meas
  · -- we assume that the result is true for a family of disjoint sets and prove it for their union
    intro f h_disj hf_meas hf
    have h_Union :
      (fun a => κ a { b : β | (a, b) ∈ ⋃ i, f i }) = fun a => κ a (⋃ i, { b : β | (a, b) ∈ f i }) :=
      by
      ext1 a
      congr with b
      simp only [Set.mem_unionᵢ, Set.supᵢ_eq_unionᵢ, Set.mem_setOf_eq]
      rfl
    rw [h_Union]
    have h_tsum :
      (fun a => κ a (⋃ i, { b : β | (a, b) ∈ f i })) = fun a =>
        ∑' i, κ a { b : β | (a, b) ∈ f i } :=
      by
      ext1 a
      rw [measure_Union]
      · intro i j hij s hsi hsj b hbs
        have habi : {(a, b)} ⊆ f i := by
          rw [Set.singleton_subset_iff]
          exact hsi hbs
        have habj : {(a, b)} ⊆ f j := by
          rw [Set.singleton_subset_iff]
          exact hsj hbs
        simpa only [Set.bot_eq_empty, Set.le_eq_subset, Set.singleton_subset_iff,
          Set.mem_empty_iff_false] using h_disj hij habi habj
      · exact fun i => (@measurable_prod_mk_left α β _ _ a) _ (hf_meas i)
    rw [h_tsum]
    exact Measurable.eNNReal_tsum hf
#align probability_theory.kernel.measurable_prod_mk_mem_of_finite ProbabilityTheory.kernel.measurable_prod_mk_mem_of_finite

theorem measurable_prod_mk_mem (κ : kernel α β) [IsSFiniteKernel κ] {t : Set (α × β)}
    (ht : MeasurableSet t) : Measurable fun a => κ a { b | (a, b) ∈ t } :=
  by
  rw [← kernel_sum_seq κ]
  have :
    ∀ a, kernel.sum (seq κ) a { b : β | (a, b) ∈ t } = ∑' n, seq κ n a { b : β | (a, b) ∈ t } :=
    fun a => kernel.sum_apply' _ _ (measurable_prod_mk_left ht)
  simp_rw [this]
  refine' Measurable.eNNReal_tsum fun n => _
  exact measurable_prod_mk_mem_of_finite (seq κ n) ht inferInstance
#align probability_theory.kernel.measurable_prod_mk_mem ProbabilityTheory.kernel.measurable_prod_mk_mem

theorem measurable_lintegral_indicator_const (κ : kernel α β) [IsSFiniteKernel κ] {t : Set (α × β)}
    (ht : MeasurableSet t) (c : ℝ≥0∞) :
    Measurable fun a => ∫⁻ b, t.indicator (Function.const (α × β) c) (a, b) ∂κ a :=
  by
  simp_rw [lintegral_indicator_const_comp measurable_prod_mk_left ht _]
  exact Measurable.const_mul (measurable_prod_mk_mem _ ht) c
#align probability_theory.kernel.measurable_lintegral_indicator_const ProbabilityTheory.kernel.measurable_lintegral_indicator_const

/-- For an s-finite kernel `κ` and a function `f : α → β → ℝ≥0∞` which is measurable when seen as a
map from `α × β` (hypothesis `measurable (function.uncurry f)`), the integral
`a ↦ ∫⁻ b, f a b ∂(κ a)` is measurable. -/
theorem measurable_lintegral (κ : kernel α β) [IsSFiniteKernel κ] {f : α → β → ℝ≥0∞}
    (hf : Measurable (Function.uncurry f)) : Measurable fun a => ∫⁻ b, f a b ∂κ a :=
  by
  let F : ℕ → simple_func (α × β) ℝ≥0∞ := simple_func.eapprox (Function.uncurry f)
  have h : ∀ a, (⨆ n, F n a) = Function.uncurry f a :=
    simple_func.supr_eapprox_apply (Function.uncurry f) hf
  simp only [Prod.forall, Function.uncurry_apply_pair] at h
  simp_rw [← h]
  have : ∀ a, (∫⁻ b, ⨆ n, F n (a, b) ∂κ a) = ⨆ n, ∫⁻ b, F n (a, b) ∂κ a :=
    by
    intro a
    rw [lintegral_supr]
    · exact fun n => (F n).Measurable.comp measurable_prod_mk_left
    · exact fun i j hij b => simple_func.monotone_eapprox (Function.uncurry f) hij _
  simp_rw [this]
  refine' measurable_supᵢ fun n => simple_func.induction _ _ (F n)
  · intro c t ht
    simp only [simple_func.const_zero, simple_func.coe_piecewise, simple_func.coe_const,
      simple_func.coe_zero, Set.piecewise_eq_indicator]
    exact measurable_lintegral_indicator_const κ ht c
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
#align probability_theory.kernel.measurable_lintegral ProbabilityTheory.kernel.measurable_lintegral

theorem measurable_lintegral' (κ : kernel α β) [IsSFiniteKernel κ] {f : β → ℝ≥0∞}
    (hf : Measurable f) : Measurable fun a => ∫⁻ b, f b ∂κ a :=
  measurable_lintegral κ (hf.comp measurable_snd)
#align probability_theory.kernel.measurable_lintegral' ProbabilityTheory.kernel.measurable_lintegral'

theorem measurableSet_lintegral (κ : kernel α β) [IsSFiniteKernel κ] {f : α → β → ℝ≥0∞}
    (hf : Measurable (Function.uncurry f)) {s : Set β} (hs : MeasurableSet s) :
    Measurable fun a => ∫⁻ b in s, f a b ∂κ a :=
  by
  simp_rw [← lintegral_restrict κ hs]
  exact measurable_lintegral _ hf
#align probability_theory.kernel.measurable_set_lintegral ProbabilityTheory.kernel.measurableSet_lintegral

theorem measurableSet_lintegral' (κ : kernel α β) [IsSFiniteKernel κ] {f : β → ℝ≥0∞}
    (hf : Measurable f) {s : Set β} (hs : MeasurableSet s) :
    Measurable fun a => ∫⁻ b in s, f b ∂κ a :=
  measurableSet_lintegral κ (hf.comp measurable_snd) hs
#align probability_theory.kernel.measurable_set_lintegral' ProbabilityTheory.kernel.measurableSet_lintegral'

end ProbabilityTheory.kernel

