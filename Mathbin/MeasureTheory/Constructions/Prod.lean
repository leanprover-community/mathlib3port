/-
Copyright (c) 2020 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn

! This file was ported from Lean 3 source module measure_theory.constructions.prod
! leanprover-community/mathlib commit 48085f140e684306f9e7da907cd5932056d1aded
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.MeasureTheory.Measure.GiryMonad
import Mathbin.Dynamics.Ergodic.MeasurePreserving
import Mathbin.MeasureTheory.Integral.SetIntegral
import Mathbin.MeasureTheory.Measure.OpenPos

/-!
# The product measure

In this file we define and prove properties about the binary product measure. If `α` and `β` have
σ-finite measures `μ` resp. `ν` then `α × β` can be equipped with a σ-finite measure `μ.prod ν` that
satisfies `(μ.prod ν) s = ∫⁻ x, ν {y | (x, y) ∈ s} ∂μ`.
We also have `(μ.prod ν) (s ×ˢ t) = μ s * ν t`, i.e. the measure of a rectangle is the product of
the measures of the sides.

We also prove Tonelli's theorem and Fubini's theorem.

## Main definition

* `measure_theory.measure.prod`: The product of two measures.

## Main results

* `measure_theory.measure.prod_apply` states `μ.prod ν s = ∫⁻ x, ν {y | (x, y) ∈ s} ∂μ`
  for measurable `s`. `measure_theory.measure.prod_apply_symm` is the reversed version.
* `measure_theory.measure.prod_prod` states `μ.prod ν (s ×ˢ t) = μ s * ν t` for measurable sets
  `s` and `t`.
* `measure_theory.lintegral_prod`: Tonelli's theorem. It states that for a measurable function
  `α × β → ℝ≥0∞` we have `∫⁻ z, f z ∂(μ.prod ν) = ∫⁻ x, ∫⁻ y, f (x, y) ∂ν ∂μ`. The version
  for functions `α → β → ℝ≥0∞` is reversed, and called `lintegral_lintegral`. Both versions have
  a variant with `_symm` appended, where the order of integration is reversed.
  The lemma `measurable.lintegral_prod_right'` states that the inner integral of the right-hand side
  is measurable.
* `measure_theory.integrable_prod_iff` states that a binary function is integrable iff both
  * `y ↦ f (x, y)` is integrable for almost every `x`, and
  * the function `x ↦ ∫ ‖f (x, y)‖ dy` is integrable.
* `measure_theory.integral_prod`: Fubini's theorem. It states that for a integrable function
  `α × β → E` (where `E` is a second countable Banach space) we have
  `∫ z, f z ∂(μ.prod ν) = ∫ x, ∫ y, f (x, y) ∂ν ∂μ`. This theorem has the same variants as
  Tonelli's theorem. The lemma `measure_theory.integrable.integral_prod_right` states that the
  inner integral of the right-hand side is integrable.

## Implementation Notes

Many results are proven twice, once for functions in curried form (`α → β → γ`) and one for
functions in uncurried form (`α × β → γ`). The former often has an assumption
`measurable (uncurry f)`, which could be inconvenient to discharge, but for the latter it is more
common that the function has to be given explicitly, since Lean cannot synthesize the function by
itself. We name the lemmas about the uncurried form with a prime.
Tonelli's theorem and Fubini's theorem have a different naming scheme, since the version for the
uncurried version is reversed.

## Tags

product measure, Fubini's theorem, Tonelli's theorem, Fubini-Tonelli theorem
-/


noncomputable section

open Classical Topology Ennreal MeasureTheory

open Set Function Real Ennreal

open MeasureTheory MeasurableSpace MeasureTheory.Measure

open TopologicalSpace hiding generateFrom

open Filter hiding prod_eq map

variable {α α' β β' γ E : Type _}

/- ./././Mathport/Syntax/Translate/Expr.lean:228:8: unsupported: ambiguous notation -/
/-- Rectangles formed by π-systems form a π-system. -/
theorem IsPiSystem.prod {C : Set (Set α)} {D : Set (Set β)} (hC : IsPiSystem C)
    (hD : IsPiSystem D) : IsPiSystem (image2 (· ×ˢ ·) C D) :=
  by
  rintro _ ⟨s₁, t₁, hs₁, ht₁, rfl⟩ _ ⟨s₂, t₂, hs₂, ht₂, rfl⟩ hst
  rw [prod_inter_prod] at hst⊢; rw [prod_nonempty_iff] at hst
  exact mem_image2_of_mem (hC _ hs₁ _ hs₂ hst.1) (hD _ ht₁ _ ht₂ hst.2)
#align is_pi_system.prod IsPiSystem.prod

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:228:8: unsupported: ambiguous notation -/
/-- Rectangles of countably spanning sets are countably spanning. -/
theorem IsCountablySpanning.prod {C : Set (Set α)} {D : Set (Set β)} (hC : IsCountablySpanning C)
    (hD : IsCountablySpanning D) : IsCountablySpanning (image2 (· ×ˢ ·) C D) :=
  by
  rcases hC, hD with ⟨⟨s, h1s, h2s⟩, t, h1t, h2t⟩
  refine' ⟨fun n => s n.unpair.1 ×ˢ t n.unpair.2, fun n => mem_image2_of_mem (h1s _) (h1t _), _⟩
  rw [Union_unpair_prod, h2s, h2t, univ_prod_univ]
#align is_countably_spanning.prod IsCountablySpanning.prod

variable [MeasurableSpace α] [MeasurableSpace α'] [MeasurableSpace β] [MeasurableSpace β']

variable [MeasurableSpace γ]

variable {μ μ' : Measure α} {ν ν' : Measure β} {τ : Measure γ}

variable [NormedAddCommGroup E]

/-! ### Measurability

Before we define the product measure, we can talk about the measurability of operations on binary
functions. We show that if `f` is a binary measurable function, then the function that integrates
along one of the variables (using either the Lebesgue or Bochner integral) is measurable.
-/


/- ./././Mathport/Syntax/Translate/Expr.lean:228:8: unsupported: ambiguous notation -/
/-- The product of generated σ-algebras is the one generated by rectangles, if both generating sets
  are countably spanning. -/
theorem generateFrom_prod_eq {α β} {C : Set (Set α)} {D : Set (Set β)} (hC : IsCountablySpanning C)
    (hD : IsCountablySpanning D) :
    @Prod.measurableSpace _ _ (generateFrom C) (generateFrom D) =
      generateFrom (image2 (· ×ˢ ·) C D) :=
  by
  apply le_antisymm
  · refine' sup_le _ _ <;> rw [comap_generate_from] <;> apply generate_from_le <;>
      rintro _ ⟨s, hs, rfl⟩
    · rcases hD with ⟨t, h1t, h2t⟩
      rw [← prod_univ, ← h2t, prod_Union]
      apply MeasurableSet.unionᵢ
      intro n
      apply measurable_set_generate_from
      exact ⟨s, t n, hs, h1t n, rfl⟩
    · rcases hC with ⟨t, h1t, h2t⟩
      rw [← univ_prod, ← h2t, Union_prod_const]
      apply MeasurableSet.unionᵢ
      rintro n
      apply measurable_set_generate_from
      exact mem_image2_of_mem (h1t n) hs
  · apply generate_from_le
    rintro _ ⟨s, t, hs, ht, rfl⟩
    rw [prod_eq]
    apply (measurable_fst _).inter (measurable_snd _)
    · exact measurable_set_generate_from hs
    · exact measurable_set_generate_from ht
#align generate_from_prod_eq generateFrom_prod_eq

/- ./././Mathport/Syntax/Translate/Expr.lean:228:8: unsupported: ambiguous notation -/
/-- If `C` and `D` generate the σ-algebras on `α` resp. `β`, then rectangles formed by `C` and `D`
  generate the σ-algebra on `α × β`. -/
theorem generateFrom_eq_prod {C : Set (Set α)} {D : Set (Set β)} (hC : generateFrom C = ‹_›)
    (hD : generateFrom D = ‹_›) (h2C : IsCountablySpanning C) (h2D : IsCountablySpanning D) :
    generateFrom (image2 (· ×ˢ ·) C D) = Prod.measurableSpace := by
  rw [← hC, ← hD, generateFrom_prod_eq h2C h2D]
#align generate_from_eq_prod generateFrom_eq_prod

/- ./././Mathport/Syntax/Translate/Expr.lean:228:8: unsupported: ambiguous notation -/
/-- The product σ-algebra is generated from boxes, i.e. `s ×ˢ t` for sets `s : set α` and
  `t : set β`. -/
theorem generateFrom_prod :
    generateFrom (image2 (· ×ˢ ·) { s : Set α | MeasurableSet s } { t : Set β | MeasurableSet t }) =
      Prod.measurableSpace :=
  generateFrom_eq_prod generateFrom_measurableSet generateFrom_measurableSet
    isCountablySpanning_measurableSet isCountablySpanning_measurableSet
#align generate_from_prod generateFrom_prod

/- ./././Mathport/Syntax/Translate/Expr.lean:228:8: unsupported: ambiguous notation -/
/-- Rectangles form a π-system. -/
theorem isPiSystem_prod :
    IsPiSystem (image2 (· ×ˢ ·) { s : Set α | MeasurableSet s } { t : Set β | MeasurableSet t }) :=
  isPiSystem_measurableSet.Prod isPiSystem_measurableSet
#align is_pi_system_prod isPiSystem_prod

/-- If `ν` is a finite measure, and `s ⊆ α × β` is measurable, then `x ↦ ν { y | (x, y) ∈ s }` is
  a measurable function. `measurable_measure_prod_mk_left` is strictly more general. -/
theorem measurable_measure_prod_mk_left_finite [IsFiniteMeasure ν] {s : Set (α × β)}
    (hs : MeasurableSet s) : Measurable fun x => ν (Prod.mk x ⁻¹' s) :=
  by
  refine' induction_on_inter generate_from_prod.symm isPiSystem_prod _ _ _ _ hs
  · simp [measurable_zero, const_def]
  · rintro _ ⟨s, t, hs, ht, rfl⟩
    simp only [mk_preimage_prod_right_eq_if, measure_if]
    exact measurable_const.indicator hs
  · intro t ht h2t
    simp_rw [preimage_compl, measure_compl (measurable_prod_mk_left ht) (measure_ne_top ν _)]
    exact h2t.const_sub _
  · intro f h1f h2f h3f
    simp_rw [preimage_Union]
    have : ∀ b, ν (⋃ i, Prod.mk b ⁻¹' f i) = ∑' i, ν (Prod.mk b ⁻¹' f i) := fun b =>
      measure_Union (fun i j hij => Disjoint.preimage _ (h1f hij)) fun i =>
        measurable_prod_mk_left (h2f i)
    simp_rw [this]
    apply Measurable.ennreal_tsum h3f
#align measurable_measure_prod_mk_left_finite measurable_measure_prod_mk_left_finite

/-- If `ν` is a σ-finite measure, and `s ⊆ α × β` is measurable, then `x ↦ ν { y | (x, y) ∈ s }` is
  a measurable function. -/
theorem measurable_measure_prod_mk_left [SigmaFinite ν] {s : Set (α × β)} (hs : MeasurableSet s) :
    Measurable fun x => ν (Prod.mk x ⁻¹' s) :=
  by
  have : ∀ x, MeasurableSet (Prod.mk x ⁻¹' s) := fun x => measurable_prod_mk_left hs
  simp only [← @supr_restrict_spanning_sets _ _ ν, this]
  apply measurable_supᵢ; intro i
  haveI := Fact.mk (measure_spanning_sets_lt_top ν i)
  exact measurable_measure_prod_mk_left_finite hs
#align measurable_measure_prod_mk_left measurable_measure_prod_mk_left

/-- If `μ` is a σ-finite measure, and `s ⊆ α × β` is measurable, then `y ↦ μ { x | (x, y) ∈ s }` is
  a measurable function. -/
theorem measurable_measure_prod_mk_right {μ : Measure α} [SigmaFinite μ] {s : Set (α × β)}
    (hs : MeasurableSet s) : Measurable fun y => μ ((fun x => (x, y)) ⁻¹' s) :=
  measurable_measure_prod_mk_left (measurableSet_swap_iff.mpr hs)
#align measurable_measure_prod_mk_right measurable_measure_prod_mk_right

theorem Measurable.map_prod_mk_left [SigmaFinite ν] : Measurable fun x : α => map (Prod.mk x) ν :=
  by
  apply measurable_of_measurable_coe; intro s hs
  simp_rw [map_apply measurable_prod_mk_left hs]
  exact measurable_measure_prod_mk_left hs
#align measurable.map_prod_mk_left Measurable.map_prod_mk_left

theorem Measurable.map_prod_mk_right {μ : Measure α} [SigmaFinite μ] :
    Measurable fun y : β => map (fun x : α => (x, y)) μ :=
  by
  apply measurable_of_measurable_coe; intro s hs
  simp_rw [map_apply measurable_prod_mk_right hs]
  exact measurable_measure_prod_mk_right hs
#align measurable.map_prod_mk_right Measurable.map_prod_mk_right

/-- The Lebesgue integral is measurable. This shows that the integrand of (the right-hand-side of)
  Tonelli's theorem is measurable. -/
theorem Measurable.lintegral_prod_right' [SigmaFinite ν] :
    ∀ {f : α × β → ℝ≥0∞} (hf : Measurable f), Measurable fun x => ∫⁻ y, f (x, y) ∂ν :=
  by
  have m := @measurable_prod_mk_left
  refine' Measurable.ennreal_induction _ _ _
  · intro c s hs
    simp only [← indicator_comp_right]
    suffices Measurable fun x => c * ν (Prod.mk x ⁻¹' s) by simpa [lintegral_indicator _ (m hs)]
    exact (measurable_measure_prod_mk_left hs).const_mul _
  · rintro f g - hf hg h2f h2g
    simp_rw [Pi.add_apply, lintegral_add_left (hf.comp m)]
    exact h2f.add h2g
  · intro f hf h2f h3f
    have := measurable_supᵢ h3f
    have : ∀ x, Monotone fun n y => f n (x, y) := fun x i j hij y => h2f hij (x, y)
    simpa [lintegral_supr fun n => (hf n).comp m, this]
#align measurable.lintegral_prod_right' Measurable.lintegral_prod_right'

/-- The Lebesgue integral is measurable. This shows that the integrand of (the right-hand-side of)
  Tonelli's theorem is measurable.
  This version has the argument `f` in curried form. -/
theorem Measurable.lintegral_prod_right [SigmaFinite ν] {f : α → β → ℝ≥0∞}
    (hf : Measurable (uncurry f)) : Measurable fun x => ∫⁻ y, f x y ∂ν :=
  hf.lintegral_prod_right'
#align measurable.lintegral_prod_right Measurable.lintegral_prod_right

/-- The Lebesgue integral is measurable. This shows that the integrand of (the right-hand-side of)
  the symmetric version of Tonelli's theorem is measurable. -/
theorem Measurable.lintegral_prod_left' [SigmaFinite μ] {f : α × β → ℝ≥0∞} (hf : Measurable f) :
    Measurable fun y => ∫⁻ x, f (x, y) ∂μ :=
  (measurable_swap_iff.mpr hf).lintegral_prod_right'
#align measurable.lintegral_prod_left' Measurable.lintegral_prod_left'

/-- The Lebesgue integral is measurable. This shows that the integrand of (the right-hand-side of)
  the symmetric version of Tonelli's theorem is measurable.
  This version has the argument `f` in curried form. -/
theorem Measurable.lintegral_prod_left [SigmaFinite μ] {f : α → β → ℝ≥0∞}
    (hf : Measurable (uncurry f)) : Measurable fun y => ∫⁻ x, f x y ∂μ :=
  hf.lintegral_prod_left'
#align measurable.lintegral_prod_left Measurable.lintegral_prod_left

theorem measurableSet_integrable [SigmaFinite ν] ⦃f : α → β → E⦄
    (hf : StronglyMeasurable (uncurry f)) : MeasurableSet { x | Integrable (f x) ν } :=
  by
  simp_rw [integrable, hf.of_uncurry_left.ae_strongly_measurable, true_and_iff]
  exact measurableSet_lt (Measurable.lintegral_prod_right hf.ennnorm) measurable_const
#align measurable_set_integrable measurableSet_integrable

section

variable [NormedSpace ℝ E] [CompleteSpace E]

/-- The Bochner integral is measurable. This shows that the integrand of (the right-hand-side of)
  Fubini's theorem is measurable.
  This version has `f` in curried form. -/
theorem MeasureTheory.StronglyMeasurable.integral_prod_right [SigmaFinite ν] ⦃f : α → β → E⦄
    (hf : StronglyMeasurable (uncurry f)) : StronglyMeasurable fun x => ∫ y, f x y ∂ν :=
  by
  borelize E
  haveI : separable_space (range (uncurry f) ∪ {0} : Set E) :=
    hf.separable_space_range_union_singleton
  let s : ℕ → simple_func (α × β) E :=
    simple_func.approx_on _ hf.measurable (range (uncurry f) ∪ {0}) 0 (by simp)
  let s' : ℕ → α → simple_func β E := fun n x => (s n).comp (Prod.mk x) measurable_prod_mk_left
  let f' : ℕ → α → E := fun n => { x | integrable (f x) ν }.indicator fun x => (s' n x).integral ν
  have hf' : ∀ n, strongly_measurable (f' n) :=
    by
    intro n
    refine' strongly_measurable.indicator _ (measurableSet_integrable hf)
    have : ∀ x, ((s' n x).range.filterₓ fun x => x ≠ 0) ⊆ (s n).range :=
      by
      intro x
      refine' Finset.Subset.trans (Finset.filter_subset _ _) _
      intro y
      simp_rw [simple_func.mem_range]
      rintro ⟨z, rfl⟩
      exact ⟨(x, z), rfl⟩
    simp only [simple_func.integral_eq_sum_of_subset (this _)]
    refine' Finset.stronglyMeasurable_sum _ fun x _ => _
    refine' (Measurable.ennreal_toReal _).StronglyMeasurable.smul_const _
    simp (config := { singlePass := true }) only [simple_func.coe_comp, preimage_comp]
    apply measurable_measure_prod_mk_left
    exact (s n).measurableSet_fiber x
  have h2f' : tendsto f' at_top (𝓝 fun x : α => ∫ y : β, f x y ∂ν) :=
    by
    rw [tendsto_pi_nhds]
    intro x
    by_cases hfx : integrable (f x) ν
    · have : ∀ n, integrable (s' n x) ν := by
        intro n
        apply (hfx.norm.add hfx.norm).mono' (s' n x).AeStronglyMeasurable
        apply eventually_of_forall
        intro y
        simp_rw [s', simple_func.coe_comp]
        exact simple_func.norm_approx_on_zero_le _ _ (x, y) n
      simp only [f', hfx, simple_func.integral_eq_integral _ (this _), indicator_of_mem,
        mem_set_of_eq]
      refine'
        tendsto_integral_of_dominated_convergence (fun y => ‖f x y‖ + ‖f x y‖)
          (fun n => (s' n x).AeStronglyMeasurable) (hfx.norm.add hfx.norm) _ _
      · exact fun n => eventually_of_forall fun y => simple_func.norm_approx_on_zero_le _ _ (x, y) n
      · refine' eventually_of_forall fun y => simple_func.tendsto_approx_on _ _ _
        apply subset_closure
        simp [-uncurry_apply_pair]
    · simp [f', hfx, integral_undef]
  exact stronglyMeasurable_of_tendsto _ hf' h2f'
#align measure_theory.strongly_measurable.integral_prod_right MeasureTheory.StronglyMeasurable.integral_prod_right

/-- The Bochner integral is measurable. This shows that the integrand of (the right-hand-side of)
  Fubini's theorem is measurable. -/
theorem MeasureTheory.StronglyMeasurable.integral_prod_right' [SigmaFinite ν] ⦃f : α × β → E⦄
    (hf : StronglyMeasurable f) : StronglyMeasurable fun x => ∫ y, f (x, y) ∂ν :=
  by
  rw [← uncurry_curry f] at hf
  exact hf.integral_prod_right
#align measure_theory.strongly_measurable.integral_prod_right' MeasureTheory.StronglyMeasurable.integral_prod_right'

/-- The Bochner integral is measurable. This shows that the integrand of (the right-hand-side of)
  the symmetric version of Fubini's theorem is measurable.
  This version has `f` in curried form. -/
theorem MeasureTheory.StronglyMeasurable.integral_prod_left [SigmaFinite μ] ⦃f : α → β → E⦄
    (hf : StronglyMeasurable (uncurry f)) : StronglyMeasurable fun y => ∫ x, f x y ∂μ :=
  (hf.compMeasurable measurable_swap).integral_prod_right'
#align measure_theory.strongly_measurable.integral_prod_left MeasureTheory.StronglyMeasurable.integral_prod_left

/-- The Bochner integral is measurable. This shows that the integrand of (the right-hand-side of)
  the symmetric version of Fubini's theorem is measurable. -/
theorem MeasureTheory.StronglyMeasurable.integral_prod_left' [SigmaFinite μ] ⦃f : α × β → E⦄
    (hf : StronglyMeasurable f) : StronglyMeasurable fun y => ∫ x, f (x, y) ∂μ :=
  (hf.compMeasurable measurable_swap).integral_prod_right'
#align measure_theory.strongly_measurable.integral_prod_left' MeasureTheory.StronglyMeasurable.integral_prod_left'

end

/-! ### The product measure -/


namespace MeasureTheory

namespace Measure

/-- The binary product of measures. They are defined for arbitrary measures, but we basically
  prove all properties under the assumption that at least one of them is σ-finite. -/
protected irreducible_def prod (μ : Measure α) (ν : Measure β) : Measure (α × β) :=
  bind μ fun x : α => map (Prod.mk x) ν
#align measure_theory.measure.prod MeasureTheory.Measure.prod

instance prod.measureSpace {α β} [MeasureSpace α] [MeasureSpace β] : MeasureSpace (α × β)
    where volume := volume.Prod volume
#align measure_theory.measure.prod.measure_space MeasureTheory.Measure.prod.measureSpace

variable [SigmaFinite ν]

theorem volume_eq_prod (α β) [MeasureSpace α] [MeasureSpace β] :
    (volume : Measure (α × β)) = (volume : Measure α).Prod (volume : Measure β) :=
  rfl
#align measure_theory.measure.volume_eq_prod MeasureTheory.Measure.volume_eq_prod

theorem prod_apply {s : Set (α × β)} (hs : MeasurableSet s) :
    μ.Prod ν s = ∫⁻ x, ν (Prod.mk x ⁻¹' s) ∂μ := by
  simp_rw [measure.prod, bind_apply hs Measurable.map_prod_mk_left,
    map_apply measurable_prod_mk_left hs]
#align measure_theory.measure.prod_apply MeasureTheory.Measure.prod_apply

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/-- The product measure of the product of two sets is the product of their measures. Note that we
do not need the sets to be measurable. -/
@[simp]
theorem prod_prod (s : Set α) (t : Set β) : μ.Prod ν (s ×ˢ t) = μ s * ν t :=
  by
  apply le_antisymm
  · set ST := to_measurable μ s ×ˢ to_measurable ν t
    have hSTm : MeasurableSet ST :=
      (measurable_set_to_measurable _ _).Prod (measurable_set_to_measurable _ _)
    calc
      μ.prod ν (s ×ˢ t) ≤ μ.prod ν ST :=
        measure_mono <| Set.prod_mono (subset_to_measurable _ _) (subset_to_measurable _ _)
      _ = μ (to_measurable μ s) * ν (to_measurable ν t) := by
        simp_rw [prod_apply hSTm, mk_preimage_prod_right_eq_if, measure_if,
          lintegral_indicator _ (measurable_set_to_measurable _ _), lintegral_const,
          restrict_apply_univ, mul_comm]
      _ = μ s * ν t := by rw [measure_to_measurable, measure_to_measurable]
      
  · -- Formalization is based on https://mathoverflow.net/a/254134/136589
    set ST := to_measurable (μ.prod ν) (s ×ˢ t)
    have hSTm : MeasurableSet ST := measurable_set_to_measurable _ _
    have hST : s ×ˢ t ⊆ ST := subset_to_measurable _ _
    set f : α → ℝ≥0∞ := fun x => ν (Prod.mk x ⁻¹' ST)
    have hfm : Measurable f := measurable_measure_prod_mk_left hSTm
    set s' : Set α := { x | ν t ≤ f x }
    have hss' : s ⊆ s' := fun x hx => measure_mono fun y hy => hST <| mk_mem_prod hx hy
    calc
      μ s * ν t ≤ μ s' * ν t := mul_le_mul_right' (measure_mono hss') _
      _ = ∫⁻ x in s', ν t ∂μ := by rw [set_lintegral_const, mul_comm]
      _ ≤ ∫⁻ x in s', f x ∂μ := set_lintegral_mono measurable_const hfm fun x => id
      _ ≤ ∫⁻ x, f x ∂μ := lintegral_mono' restrict_le_self le_rfl
      _ = μ.prod ν ST := (prod_apply hSTm).symm
      _ = μ.prod ν (s ×ˢ t) := measure_to_measurable _
      
#align measure_theory.measure.prod_prod MeasureTheory.Measure.prod_prod

instance {X Y : Type _} [TopologicalSpace X] [TopologicalSpace Y] {m : MeasurableSpace X}
    {μ : Measure X} [IsOpenPosMeasure μ] {m' : MeasurableSpace Y} {ν : Measure Y}
    [IsOpenPosMeasure ν] [SigmaFinite ν] : IsOpenPosMeasure (μ.Prod ν) :=
  by
  constructor
  rintro U U_open ⟨⟨x, y⟩, hxy⟩
  rcases isOpen_prod_iff.1 U_open x y hxy with ⟨u, v, u_open, v_open, xu, yv, huv⟩
  refine' ne_of_gt (lt_of_lt_of_le _ (measure_mono huv))
  simp only [prod_prod, CanonicallyOrderedCommSemiring.mul_pos]
  constructor
  · exact u_open.measure_pos μ ⟨x, xu⟩
  · exact v_open.measure_pos ν ⟨y, yv⟩

instance {α β : Type _} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} (μ : Measure α)
    (ν : Measure β) [IsFiniteMeasure μ] [IsFiniteMeasure ν] : IsFiniteMeasure (μ.Prod ν) :=
  by
  constructor
  rw [← univ_prod_univ, prod_prod]
  exact mul_lt_top (measure_lt_top _ _).Ne (measure_lt_top _ _).Ne

instance {α β : Type _} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} (μ : Measure α)
    (ν : Measure β) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    IsProbabilityMeasure (μ.Prod ν) :=
  ⟨by rw [← univ_prod_univ, prod_prod, measure_univ, measure_univ, mul_one]⟩

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
instance {α β : Type _} [TopologicalSpace α] [TopologicalSpace β] {mα : MeasurableSpace α}
    {mβ : MeasurableSpace β} (μ : Measure α) (ν : Measure β) [IsFiniteMeasureOnCompacts μ]
    [IsFiniteMeasureOnCompacts ν] [SigmaFinite ν] : IsFiniteMeasureOnCompacts (μ.Prod ν) :=
  by
  refine' ⟨fun K hK => _⟩
  set L := (Prod.fst '' K) ×ˢ (Prod.snd '' K) with hL
  have : K ⊆ L := by
    rintro ⟨x, y⟩ hxy
    simp only [prod_mk_mem_set_prod_eq, mem_image, Prod.exists, exists_and_right, exists_eq_right]
    exact ⟨⟨y, hxy⟩, ⟨x, hxy⟩⟩
  apply lt_of_le_of_lt (measure_mono this)
  rw [hL, prod_prod]
  exact
    mul_lt_top (IsCompact.measure_lt_top (hK.image continuous_fst)).Ne
      (IsCompact.measure_lt_top (hK.image continuous_snd)).Ne

theorem ae_measure_lt_top {s : Set (α × β)} (hs : MeasurableSet s) (h2s : (μ.Prod ν) s ≠ ∞) :
    ∀ᵐ x ∂μ, ν (Prod.mk x ⁻¹' s) < ∞ :=
  by
  simp_rw [prod_apply hs] at h2s
  refine' ae_lt_top (measurable_measure_prod_mk_left hs) h2s
#align measure_theory.measure.ae_measure_lt_top MeasureTheory.Measure.ae_measure_lt_top

theorem integrableMeasureProdMkLeft {s : Set (α × β)} (hs : MeasurableSet s)
    (h2s : (μ.Prod ν) s ≠ ∞) : Integrable (fun x => (ν (Prod.mk x ⁻¹' s)).toReal) μ :=
  by
  refine' ⟨(measurable_measure_prod_mk_left hs).ennreal_toReal.AeMeasurable.AeStronglyMeasurable, _⟩
  simp_rw [has_finite_integral, ennnorm_eq_of_real to_real_nonneg]
  convert h2s.lt_top using 1; simp_rw [prod_apply hs]; apply lintegral_congr_ae
  refine' (ae_measure_lt_top hs h2s).mp _; apply eventually_of_forall; intro x hx
  rw [lt_top_iff_ne_top] at hx; simp [of_real_to_real, hx]
#align measure_theory.measure.integrable_measure_prod_mk_left MeasureTheory.Measure.integrableMeasureProdMkLeft

/-- Note: the assumption `hs` cannot be dropped. For a counterexample, see
  Walter Rudin *Real and Complex Analysis*, example (c) in section 8.9. -/
theorem measure_prod_null {s : Set (α × β)} (hs : MeasurableSet s) :
    μ.Prod ν s = 0 ↔ (fun x => ν (Prod.mk x ⁻¹' s)) =ᵐ[μ] 0 := by
  simp_rw [prod_apply hs, lintegral_eq_zero_iff (measurable_measure_prod_mk_left hs)]
#align measure_theory.measure.measure_prod_null MeasureTheory.Measure.measure_prod_null

/-- Note: the converse is not true without assuming that `s` is measurable. For a counterexample,
  see Walter Rudin *Real and Complex Analysis*, example (c) in section 8.9. -/
theorem measure_ae_null_of_prod_null {s : Set (α × β)} (h : μ.Prod ν s = 0) :
    (fun x => ν (Prod.mk x ⁻¹' s)) =ᵐ[μ] 0 :=
  by
  obtain ⟨t, hst, mt, ht⟩ := exists_measurable_superset_of_null h
  simp_rw [measure_prod_null mt] at ht
  rw [eventually_le_antisymm_iff]
  exact
    ⟨eventually_le.trans_eq (eventually_of_forall fun x => (measure_mono (preimage_mono hst) : _))
        ht,
      eventually_of_forall fun x => zero_le _⟩
#align measure_theory.measure.measure_ae_null_of_prod_null MeasureTheory.Measure.measure_ae_null_of_prod_null

theorem AbsolutelyContinuous.prod [SigmaFinite ν'] (h1 : μ ≪ μ') (h2 : ν ≪ ν') :
    μ.Prod ν ≪ μ'.Prod ν' :=
  by
  refine' absolutely_continuous.mk fun s hs h2s => _
  simp_rw [measure_prod_null hs] at h2s⊢
  exact (h2s.filter_mono h1.ae_le).mono fun _ h => h2 h
#align measure_theory.measure.absolutely_continuous.prod MeasureTheory.Measure.AbsolutelyContinuous.prod

/-- Note: the converse is not true. For a counterexample, see
  Walter Rudin *Real and Complex Analysis*, example (c) in section 8.9. -/
theorem ae_ae_of_ae_prod {p : α × β → Prop} (h : ∀ᵐ z ∂μ.Prod ν, p z) :
    ∀ᵐ x ∂μ, ∀ᵐ y ∂ν, p (x, y) :=
  measure_ae_null_of_prod_null h
#align measure_theory.measure.ae_ae_of_ae_prod MeasureTheory.Measure.ae_ae_of_ae_prod

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:228:8: unsupported: ambiguous notation -/
/-- `μ.prod ν` has finite spanning sets in rectangles of finite spanning sets. -/
noncomputable def FiniteSpanningSetsIn.prod {ν : Measure β} {C : Set (Set α)} {D : Set (Set β)}
    (hμ : μ.FiniteSpanningSetsIn C) (hν : ν.FiniteSpanningSetsIn D) :
    (μ.Prod ν).FiniteSpanningSetsIn (image2 (· ×ˢ ·) C D) :=
  by
  haveI := hν.sigma_finite
  refine'
    ⟨fun n => hμ.set n.unpair.1 ×ˢ hν.set n.unpair.2, fun n =>
      mem_image2_of_mem (hμ.set_mem _) (hν.set_mem _), fun n => _, _⟩
  · rw [prod_prod]
    exact mul_lt_top (hμ.finite _).Ne (hν.finite _).Ne
  · simp_rw [Union_unpair_prod, hμ.spanning, hν.spanning, univ_prod_univ]
#align measure_theory.measure.finite_spanning_sets_in.prod MeasureTheory.Measure.FiniteSpanningSetsIn.prod

theorem quasiMeasurePreservingFst : QuasiMeasurePreserving Prod.fst (μ.Prod ν) μ :=
  by
  refine' ⟨measurable_fst, absolutely_continuous.mk fun s hs h2s => _⟩
  rw [map_apply measurable_fst hs, ← prod_univ, prod_prod, h2s, zero_mul]
#align measure_theory.measure.quasi_measure_preserving_fst MeasureTheory.Measure.quasiMeasurePreservingFst

theorem quasiMeasurePreservingSnd : QuasiMeasurePreserving Prod.snd (μ.Prod ν) ν :=
  by
  refine' ⟨measurable_snd, absolutely_continuous.mk fun s hs h2s => _⟩
  rw [map_apply measurable_snd hs, ← univ_prod, prod_prod, h2s, mul_zero]
#align measure_theory.measure.quasi_measure_preserving_snd MeasureTheory.Measure.quasiMeasurePreservingSnd

variable [SigmaFinite μ]

instance prod.sigmaFinite : SigmaFinite (μ.Prod ν) :=
  (μ.toFiniteSpanningSetsIn.Prod ν.toFiniteSpanningSetsIn).SigmaFinite
#align measure_theory.measure.prod.sigma_finite MeasureTheory.Measure.prod.sigmaFinite

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/-- A measure on a product space equals the product measure if they are equal on rectangles
  with as sides sets that generate the corresponding σ-algebras. -/
theorem prod_eq_generateFrom {μ : Measure α} {ν : Measure β} {C : Set (Set α)} {D : Set (Set β)}
    (hC : generateFrom C = ‹_›) (hD : generateFrom D = ‹_›) (h2C : IsPiSystem C)
    (h2D : IsPiSystem D) (h3C : μ.FiniteSpanningSetsIn C) (h3D : ν.FiniteSpanningSetsIn D)
    {μν : Measure (α × β)} (h₁ : ∀ s ∈ C, ∀ t ∈ D, μν (s ×ˢ t) = μ s * ν t) : μ.Prod ν = μν :=
  by
  refine'
    (h3C.prod h3D).ext
      (generateFrom_eq_prod hC hD h3C.is_countably_spanning h3D.is_countably_spanning).symm
      (h2C.prod h2D) _
  · rintro _ ⟨s, t, hs, ht, rfl⟩
    haveI := h3D.sigma_finite
    rw [h₁ s hs t ht, prod_prod]
#align measure_theory.measure.prod_eq_generate_from MeasureTheory.Measure.prod_eq_generateFrom

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/-- A measure on a product space equals the product measure if they are equal on rectangles. -/
theorem prod_eq {μν : Measure (α × β)}
    (h : ∀ s t, MeasurableSet s → MeasurableSet t → μν (s ×ˢ t) = μ s * ν t) : μ.Prod ν = μν :=
  prod_eq_generateFrom generateFrom_measurableSet generateFrom_measurableSet
    isPiSystem_measurableSet isPiSystem_measurableSet μ.toFiniteSpanningSetsIn
    ν.toFiniteSpanningSetsIn fun s hs t ht => h s t hs ht
#align measure_theory.measure.prod_eq MeasureTheory.Measure.prod_eq

theorem prod_swap : map Prod.swap (μ.Prod ν) = ν.Prod μ :=
  by
  refine' (prod_eq _).symm
  intro s t hs ht
  simp_rw [map_apply measurable_swap (hs.prod ht), preimage_swap_prod, prod_prod, mul_comm]
#align measure_theory.measure.prod_swap MeasureTheory.Measure.prod_swap

theorem measurePreservingSwap : MeasurePreserving Prod.swap (μ.Prod ν) (ν.Prod μ) :=
  ⟨measurable_swap, prod_swap⟩
#align measure_theory.measure.measure_preserving_swap MeasureTheory.Measure.measurePreservingSwap

theorem prod_apply_symm {s : Set (α × β)} (hs : MeasurableSet s) :
    μ.Prod ν s = ∫⁻ y, μ ((fun x => (x, y)) ⁻¹' s) ∂ν :=
  by
  rw [← prod_swap, map_apply measurable_swap hs]
  simp only [prod_apply (measurable_swap hs)]
  rfl
#align measure_theory.measure.prod_apply_symm MeasureTheory.Measure.prod_apply_symm

theorem prodAssoc_prod [SigmaFinite τ] :
    map MeasurableEquiv.prodAssoc ((μ.Prod ν).Prod τ) = μ.Prod (ν.Prod τ) :=
  by
  refine'
    (prod_eq_generateFrom generate_from_measurable_set generateFrom_prod is_pi_system_measurable_set
        isPiSystem_prod μ.to_finite_spanning_sets_in
        (ν.to_finite_spanning_sets_in.prod τ.to_finite_spanning_sets_in) _).symm
  rintro s hs _ ⟨t, u, ht, hu, rfl⟩; rw [mem_set_of_eq] at hs ht hu
  simp_rw [map_apply (MeasurableEquiv.measurable _) (hs.prod (ht.prod hu)),
    MeasurableEquiv.prodAssoc, MeasurableEquiv.coe_mk, Equiv.prod_assoc_preimage, prod_prod,
    mul_assoc]
#align measure_theory.measure.prod_assoc_prod MeasureTheory.Measure.prodAssoc_prod

/-! ### The product of specific measures -/


/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem prod_restrict (s : Set α) (t : Set β) :
    (μ.restrict s).Prod (ν.restrict t) = (μ.Prod ν).restrict (s ×ˢ t) :=
  by
  refine' prod_eq fun s' t' hs' ht' => _
  rw [restrict_apply (hs'.prod ht'), prod_inter_prod, prod_prod, restrict_apply hs',
    restrict_apply ht']
#align measure_theory.measure.prod_restrict MeasureTheory.Measure.prod_restrict

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem restrict_prod_eq_prod_univ (s : Set α) :
    (μ.restrict s).Prod ν = (μ.Prod ν).restrict (s ×ˢ (univ : Set β)) :=
  by
  have : ν = ν.restrict Set.univ := measure.restrict_univ.symm
  rwa [this, measure.prod_restrict, ← this]
#align measure_theory.measure.restrict_prod_eq_prod_univ MeasureTheory.Measure.restrict_prod_eq_prod_univ

theorem prod_dirac (y : β) : μ.Prod (dirac y) = map (fun x => (x, y)) μ :=
  by
  refine' prod_eq fun s t hs ht => _
  simp_rw [map_apply measurable_prod_mk_right (hs.prod ht), mk_preimage_prod_left_eq_if, measure_if,
    dirac_apply' _ ht, ← indicator_mul_right _ fun x => μ s, Pi.one_apply, mul_one]
#align measure_theory.measure.prod_dirac MeasureTheory.Measure.prod_dirac

theorem dirac_prod (x : α) : (dirac x).Prod ν = map (Prod.mk x) ν :=
  by
  refine' prod_eq fun s t hs ht => _
  simp_rw [map_apply measurable_prod_mk_left (hs.prod ht), mk_preimage_prod_right_eq_if, measure_if,
    dirac_apply' _ hs, ← indicator_mul_left _ _ fun x => ν t, Pi.one_apply, one_mul]
#align measure_theory.measure.dirac_prod MeasureTheory.Measure.dirac_prod

theorem dirac_prod_dirac {x : α} {y : β} : (dirac x).Prod (dirac y) = dirac (x, y) := by
  rw [prod_dirac, map_dirac measurable_prod_mk_right]
#align measure_theory.measure.dirac_prod_dirac MeasureTheory.Measure.dirac_prod_dirac

theorem prod_sum {ι : Type _} [Finite ι] (ν : ι → Measure β) [∀ i, SigmaFinite (ν i)] :
    μ.Prod (sum ν) = sum fun i => μ.Prod (ν i) :=
  by
  refine' prod_eq fun s t hs ht => _
  simp_rw [sum_apply _ (hs.prod ht), sum_apply _ ht, prod_prod, Ennreal.tsum_mul_left]
#align measure_theory.measure.prod_sum MeasureTheory.Measure.prod_sum

theorem sum_prod {ι : Type _} [Finite ι] (μ : ι → Measure α) [∀ i, SigmaFinite (μ i)] :
    (sum μ).Prod ν = sum fun i => (μ i).Prod ν :=
  by
  refine' prod_eq fun s t hs ht => _
  simp_rw [sum_apply _ (hs.prod ht), sum_apply _ hs, prod_prod, Ennreal.tsum_mul_right]
#align measure_theory.measure.sum_prod MeasureTheory.Measure.sum_prod

theorem prod_add (ν' : Measure β) [SigmaFinite ν'] : μ.Prod (ν + ν') = μ.Prod ν + μ.Prod ν' :=
  by
  refine' prod_eq fun s t hs ht => _
  simp_rw [add_apply, prod_prod, left_distrib]
#align measure_theory.measure.prod_add MeasureTheory.Measure.prod_add

theorem add_prod (μ' : Measure α) [SigmaFinite μ'] : (μ + μ').Prod ν = μ.Prod ν + μ'.Prod ν :=
  by
  refine' prod_eq fun s t hs ht => _
  simp_rw [add_apply, prod_prod, right_distrib]
#align measure_theory.measure.add_prod MeasureTheory.Measure.add_prod

@[simp]
theorem zero_prod (ν : Measure β) : (0 : Measure α).Prod ν = 0 :=
  by
  rw [measure.prod]
  exact bind_zero_left _
#align measure_theory.measure.zero_prod MeasureTheory.Measure.zero_prod

@[simp]
theorem prod_zero (μ : Measure α) : μ.Prod (0 : Measure β) = 0 := by simp [measure.prod]
#align measure_theory.measure.prod_zero MeasureTheory.Measure.prod_zero

theorem map_prod_map {δ} [MeasurableSpace δ] {f : α → β} {g : γ → δ} {μa : Measure α}
    {μc : Measure γ} (hfa : SigmaFinite (map f μa)) (hgc : SigmaFinite (map g μc))
    (hf : Measurable f) (hg : Measurable g) :
    (map f μa).Prod (map g μc) = map (Prod.map f g) (μa.Prod μc) :=
  by
  haveI := hgc.of_map μc hg.ae_measurable
  refine' prod_eq fun s t hs ht => _
  rw [map_apply (hf.prod_map hg) (hs.prod ht), map_apply hf hs, map_apply hg ht]
  exact prod_prod (f ⁻¹' s) (g ⁻¹' t)
#align measure_theory.measure.map_prod_map MeasureTheory.Measure.map_prod_map

end Measure

open Measure

namespace MeasurePreserving

variable {δ : Type _} [MeasurableSpace δ] {μa : Measure α} {μb : Measure β} {μc : Measure γ}
  {μd : Measure δ}

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem skewProduct [SigmaFinite μb] [SigmaFinite μd] {f : α → β} (hf : MeasurePreserving f μa μb)
    {g : α → γ → δ} (hgm : Measurable (uncurry g)) (hg : ∀ᵐ x ∂μa, map (g x) μc = μd) :
    MeasurePreserving (fun p : α × γ => (f p.1, g p.1 p.2)) (μa.Prod μc) (μb.Prod μd) := by
  classical
    have : Measurable fun p : α × γ => (f p.1, g p.1 p.2) := (hf.1.comp measurable_fst).prod_mk hgm
    /- if `μa = 0`, then the lemma is trivial, otherwise we can use `hg`
      to deduce `sigma_finite μc`. -/
    rcases eq_or_ne μa 0 with (rfl | ha)
    · rw [← hf.map_eq, zero_prod, measure.map_zero, zero_prod]
      exact ⟨this, by simp only [measure.map_zero]⟩
    have : sigma_finite μc :=
      by
      rcases(ae_ne_bot.2 ha).nonempty_of_mem hg with ⟨x, hx : map (g x) μc = μd⟩
      exact sigma_finite.of_map _ hgm.of_uncurry_left.ae_measurable (by rwa [hx])
    -- Thus we can apply `measure.prod_eq` to prove equality of measures.
    refine' ⟨this, (prod_eq fun s t hs ht => _).symm⟩
    rw [map_apply this (hs.prod ht)]
    refine' (prod_apply (this <| hs.prod ht)).trans _
    have :
      ∀ᵐ x ∂μa, μc ((fun y => (f x, g x y)) ⁻¹' s ×ˢ t) = indicator (f ⁻¹' s) (fun y => μd t) x :=
      by
      refine' hg.mono fun x hx => _
      subst hx
      simp only [mk_preimage_prod_right_fn_eq_if, indicator_apply, mem_preimage]
      split_ifs
      exacts[(map_apply hgm.of_uncurry_left ht).symm, measure_empty]
    simp only [preimage_preimage]
    rw [lintegral_congr_ae this, lintegral_indicator _ (hf.1 hs), set_lintegral_const,
      hf.measure_preimage hs, mul_comm]
#align measure_theory.measure_preserving.skew_product MeasureTheory.MeasurePreserving.skewProduct

/-- If `f : α → β` sends the measure `μa` to `μb` and `g : γ → δ` sends the measure `μc` to `μd`,
then `prod.map f g` sends `μa.prod μc` to `μb.prod μd`. -/
protected theorem prod [SigmaFinite μb] [SigmaFinite μd] {f : α → β} {g : γ → δ}
    (hf : MeasurePreserving f μa μb) (hg : MeasurePreserving g μc μd) :
    MeasurePreserving (Prod.map f g) (μa.Prod μc) (μb.Prod μd) :=
  have : Measurable (uncurry fun _ : α => g) := hg.1.comp measurable_snd
  hf.skewProduct this <| Filter.eventually_of_forall fun _ => hg.map_eq
#align measure_theory.measure_preserving.prod MeasureTheory.MeasurePreserving.prod

end MeasurePreserving

namespace QuasiMeasurePreserving

theorem prodOfRight {f : α × β → γ} {μ : Measure α} {ν : Measure β} {τ : Measure γ}
    (hf : Measurable f) [SigmaFinite ν]
    (h2f : ∀ᵐ x ∂μ, QuasiMeasurePreserving (fun y => f (x, y)) ν τ) :
    QuasiMeasurePreserving f (μ.Prod ν) τ :=
  by
  refine' ⟨hf, _⟩
  refine' absolutely_continuous.mk fun s hs h2s => _
  simp_rw [map_apply hf hs, prod_apply (hf hs), preimage_preimage,
    lintegral_congr_ae (h2f.mono fun x hx => hx.preimage_null h2s), lintegral_zero]
#align measure_theory.quasi_measure_preserving.prod_of_right MeasureTheory.QuasiMeasurePreserving.prodOfRight

theorem prodOfLeft {α β γ} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    {f : α × β → γ} {μ : Measure α} {ν : Measure β} {τ : Measure γ} (hf : Measurable f)
    [SigmaFinite μ] [SigmaFinite ν]
    (h2f : ∀ᵐ y ∂ν, QuasiMeasurePreserving (fun x => f (x, y)) μ τ) :
    QuasiMeasurePreserving f (μ.Prod ν) τ :=
  by
  rw [← prod_swap]
  convert
    (quasi_measure_preserving.prod_of_right (hf.comp measurable_swap) h2f).comp
      ((measurable_swap.measure_preserving (ν.prod μ)).symm
          MeasurableEquiv.prodComm).QuasiMeasurePreserving
  ext ⟨x, y⟩; rfl
#align measure_theory.quasi_measure_preserving.prod_of_left MeasureTheory.QuasiMeasurePreserving.prodOfLeft

end QuasiMeasurePreserving

end MeasureTheory

open MeasureTheory.Measure

section

theorem AeMeasurable.prodSwap [SigmaFinite μ] [SigmaFinite ν] {f : β × α → γ}
    (hf : AeMeasurable f (ν.Prod μ)) : AeMeasurable (fun z : α × β => f z.symm) (μ.Prod ν) :=
  by
  rw [← prod_swap] at hf
  exact hf.comp_measurable measurable_swap
#align ae_measurable.prod_swap AeMeasurable.prodSwap

theorem MeasureTheory.AeStronglyMeasurable.prodSwap {γ : Type _} [TopologicalSpace γ]
    [SigmaFinite μ] [SigmaFinite ν] {f : β × α → γ} (hf : AeStronglyMeasurable f (ν.Prod μ)) :
    AeStronglyMeasurable (fun z : α × β => f z.symm) (μ.Prod ν) :=
  by
  rw [← prod_swap] at hf
  exact hf.comp_measurable measurable_swap
#align measure_theory.ae_strongly_measurable.prod_swap MeasureTheory.AeStronglyMeasurable.prodSwap

theorem AeMeasurable.fst [SigmaFinite ν] {f : α → γ} (hf : AeMeasurable f μ) :
    AeMeasurable (fun z : α × β => f z.1) (μ.Prod ν) :=
  hf.compQuasiMeasurePreserving quasiMeasurePreservingFst
#align ae_measurable.fst AeMeasurable.fst

theorem AeMeasurable.snd [SigmaFinite ν] {f : β → γ} (hf : AeMeasurable f ν) :
    AeMeasurable (fun z : α × β => f z.2) (μ.Prod ν) :=
  hf.compQuasiMeasurePreserving quasiMeasurePreservingSnd
#align ae_measurable.snd AeMeasurable.snd

theorem MeasureTheory.AeStronglyMeasurable.fst {γ} [TopologicalSpace γ] [SigmaFinite ν] {f : α → γ}
    (hf : AeStronglyMeasurable f μ) : AeStronglyMeasurable (fun z : α × β => f z.1) (μ.Prod ν) :=
  hf.compQuasiMeasurePreserving quasiMeasurePreservingFst
#align measure_theory.ae_strongly_measurable.fst MeasureTheory.AeStronglyMeasurable.fst

theorem MeasureTheory.AeStronglyMeasurable.snd {γ} [TopologicalSpace γ] [SigmaFinite ν] {f : β → γ}
    (hf : AeStronglyMeasurable f ν) : AeStronglyMeasurable (fun z : α × β => f z.2) (μ.Prod ν) :=
  hf.compQuasiMeasurePreserving quasiMeasurePreservingSnd
#align measure_theory.ae_strongly_measurable.snd MeasureTheory.AeStronglyMeasurable.snd

/-- The Bochner integral is a.e.-measurable.
  This shows that the integrand of (the right-hand-side of) Fubini's theorem is a.e.-measurable. -/
theorem MeasureTheory.AeStronglyMeasurable.integralProdRight' [SigmaFinite ν] [NormedSpace ℝ E]
    [CompleteSpace E] ⦃f : α × β → E⦄ (hf : AeStronglyMeasurable f (μ.Prod ν)) :
    AeStronglyMeasurable (fun x => ∫ y, f (x, y) ∂ν) μ :=
  ⟨fun x => ∫ y, hf.mk f (x, y) ∂ν, hf.stronglyMeasurable_mk.integral_prod_right', by
    filter_upwards [ae_ae_of_ae_prod hf.ae_eq_mk]with _ hx using integral_congr_ae hx⟩
#align measure_theory.ae_strongly_measurable.integral_prod_right' MeasureTheory.AeStronglyMeasurable.integralProdRight'

theorem MeasureTheory.AeStronglyMeasurable.prod_mk_left {γ : Type _} [SigmaFinite ν]
    [TopologicalSpace γ] {f : α × β → γ} (hf : AeStronglyMeasurable f (μ.Prod ν)) :
    ∀ᵐ x ∂μ, AeStronglyMeasurable (fun y => f (x, y)) ν :=
  by
  filter_upwards [ae_ae_of_ae_prod hf.ae_eq_mk]with x hx
  exact
    ⟨fun y => hf.mk f (x, y), hf.strongly_measurable_mk.comp_measurable measurable_prod_mk_left, hx⟩
#align measure_theory.ae_strongly_measurable.prod_mk_left MeasureTheory.AeStronglyMeasurable.prod_mk_left

end

namespace MeasureTheory

/-! ### The Lebesgue integral on a product -/


variable [SigmaFinite ν]

theorem lintegral_prod_swap [SigmaFinite μ] (f : α × β → ℝ≥0∞) (hf : AeMeasurable f (μ.Prod ν)) :
    (∫⁻ z, f z.symm ∂ν.Prod μ) = ∫⁻ z, f z ∂μ.Prod ν :=
  by
  rw [← prod_swap] at hf
  rw [← lintegral_map' hf measurable_swap.ae_measurable, prod_swap]
#align measure_theory.lintegral_prod_swap MeasureTheory.lintegral_prod_swap

/-- **Tonelli's Theorem**: For `ℝ≥0∞`-valued measurable functions on `α × β`,
  the integral of `f` is equal to the iterated integral. -/
theorem lintegral_prod_of_measurable :
    ∀ (f : α × β → ℝ≥0∞) (hf : Measurable f), (∫⁻ z, f z ∂μ.Prod ν) = ∫⁻ x, ∫⁻ y, f (x, y) ∂ν ∂μ :=
  by
  have m := @measurable_prod_mk_left
  refine' Measurable.ennreal_induction _ _ _
  · intro c s hs
    simp only [← indicator_comp_right]
    simp [lintegral_indicator, m hs, hs, lintegral_const_mul, measurable_measure_prod_mk_left hs,
      prod_apply]
  · rintro f g - hf hg h2f h2g
    simp [lintegral_add_left, Measurable.lintegral_prod_right', hf.comp m, hf, h2f, h2g]
  · intro f hf h2f h3f
    have kf : ∀ x n, Measurable fun y => f n (x, y) := fun x n => (hf n).comp m
    have k2f : ∀ x, Monotone fun n y => f n (x, y) := fun x i j hij y => h2f hij (x, y)
    have lf : ∀ n, Measurable fun x => ∫⁻ y, f n (x, y) ∂ν := fun n => (hf n).lintegral_prod_right'
    have l2f : Monotone fun n x => ∫⁻ y, f n (x, y) ∂ν := fun i j hij x =>
      lintegral_mono (k2f x hij)
    simp only [lintegral_supr hf h2f, lintegral_supr (kf _), k2f, lintegral_supr lf l2f, h3f]
#align measure_theory.lintegral_prod_of_measurable MeasureTheory.lintegral_prod_of_measurable

/-- **Tonelli's Theorem**: For `ℝ≥0∞`-valued almost everywhere measurable functions on `α × β`,
  the integral of `f` is equal to the iterated integral. -/
theorem lintegral_prod (f : α × β → ℝ≥0∞) (hf : AeMeasurable f (μ.Prod ν)) :
    (∫⁻ z, f z ∂μ.Prod ν) = ∫⁻ x, ∫⁻ y, f (x, y) ∂ν ∂μ :=
  by
  have A : (∫⁻ z, f z ∂μ.prod ν) = ∫⁻ z, hf.mk f z ∂μ.prod ν := lintegral_congr_ae hf.ae_eq_mk
  have B : (∫⁻ x, ∫⁻ y, f (x, y) ∂ν ∂μ) = ∫⁻ x, ∫⁻ y, hf.mk f (x, y) ∂ν ∂μ :=
    by
    apply lintegral_congr_ae
    filter_upwards [ae_ae_of_ae_prod hf.ae_eq_mk]with _ ha using lintegral_congr_ae ha
  rw [A, B, lintegral_prod_of_measurable _ hf.measurable_mk]
  infer_instance
#align measure_theory.lintegral_prod MeasureTheory.lintegral_prod

/-- The symmetric verion of Tonelli's Theorem: For `ℝ≥0∞`-valued almost everywhere measurable
functions on `α × β`,  the integral of `f` is equal to the iterated integral, in reverse order. -/
theorem lintegral_prod_symm [SigmaFinite μ] (f : α × β → ℝ≥0∞) (hf : AeMeasurable f (μ.Prod ν)) :
    (∫⁻ z, f z ∂μ.Prod ν) = ∫⁻ y, ∫⁻ x, f (x, y) ∂μ ∂ν :=
  by
  simp_rw [← lintegral_prod_swap f hf]
  exact lintegral_prod _ hf.prod_swap
#align measure_theory.lintegral_prod_symm MeasureTheory.lintegral_prod_symm

/-- The symmetric verion of Tonelli's Theorem: For `ℝ≥0∞`-valued measurable
functions on `α × β`,  the integral of `f` is equal to the iterated integral, in reverse order. -/
theorem lintegral_prod_symm' [SigmaFinite μ] (f : α × β → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ z, f z ∂μ.Prod ν) = ∫⁻ y, ∫⁻ x, f (x, y) ∂μ ∂ν :=
  lintegral_prod_symm f hf.AeMeasurable
#align measure_theory.lintegral_prod_symm' MeasureTheory.lintegral_prod_symm'

/-- The reversed version of **Tonelli's Theorem**. In this version `f` is in curried form, which
makes it easier for the elaborator to figure out `f` automatically. -/
theorem lintegral_lintegral ⦃f : α → β → ℝ≥0∞⦄ (hf : AeMeasurable (uncurry f) (μ.Prod ν)) :
    (∫⁻ x, ∫⁻ y, f x y ∂ν ∂μ) = ∫⁻ z, f z.1 z.2 ∂μ.Prod ν :=
  (lintegral_prod _ hf).symm
#align measure_theory.lintegral_lintegral MeasureTheory.lintegral_lintegral

/-- The reversed version of **Tonelli's Theorem** (symmetric version). In this version `f` is in
curried form, which makes it easier for the elaborator to figure out `f` automatically. -/
theorem lintegral_lintegral_symm [SigmaFinite μ] ⦃f : α → β → ℝ≥0∞⦄
    (hf : AeMeasurable (uncurry f) (μ.Prod ν)) :
    (∫⁻ x, ∫⁻ y, f x y ∂ν ∂μ) = ∫⁻ z, f z.2 z.1 ∂ν.Prod μ :=
  (lintegral_prod_symm _ hf.prod_swap).symm
#align measure_theory.lintegral_lintegral_symm MeasureTheory.lintegral_lintegral_symm

/-- Change the order of Lebesgue integration. -/
theorem lintegral_lintegral_swap [SigmaFinite μ] ⦃f : α → β → ℝ≥0∞⦄
    (hf : AeMeasurable (uncurry f) (μ.Prod ν)) :
    (∫⁻ x, ∫⁻ y, f x y ∂ν ∂μ) = ∫⁻ y, ∫⁻ x, f x y ∂μ ∂ν :=
  (lintegral_lintegral hf).trans (lintegral_prod_symm _ hf)
#align measure_theory.lintegral_lintegral_swap MeasureTheory.lintegral_lintegral_swap

theorem lintegral_prod_mul {f : α → ℝ≥0∞} {g : β → ℝ≥0∞} (hf : AeMeasurable f μ)
    (hg : AeMeasurable g ν) : (∫⁻ z, f z.1 * g z.2 ∂μ.Prod ν) = (∫⁻ x, f x ∂μ) * ∫⁻ y, g y ∂ν := by
  simp [lintegral_prod _ (hf.fst.mul hg.snd), lintegral_lintegral_mul hf hg]
#align measure_theory.lintegral_prod_mul MeasureTheory.lintegral_prod_mul

/-! ### Integrability on a product -/


section

theorem Integrable.swap [SigmaFinite μ] ⦃f : α × β → E⦄ (hf : Integrable f (μ.Prod ν)) :
    Integrable (f ∘ Prod.swap) (ν.Prod μ) :=
  ⟨hf.AeStronglyMeasurable.prod_swap,
    (lintegral_prod_swap _ hf.AeStronglyMeasurable.ennnorm : _).le.trans_lt hf.HasFiniteIntegral⟩
#align measure_theory.integrable.swap MeasureTheory.Integrable.swap

theorem integrable_swap_iff [SigmaFinite μ] ⦃f : α × β → E⦄ :
    Integrable (f ∘ Prod.swap) (ν.Prod μ) ↔ Integrable f (μ.Prod ν) :=
  ⟨fun hf => by
    convert hf.swap
    ext ⟨x, y⟩
    rfl, fun hf => hf.symm⟩
#align measure_theory.integrable_swap_iff MeasureTheory.integrable_swap_iff

theorem hasFiniteIntegral_prod_iff ⦃f : α × β → E⦄ (h1f : StronglyMeasurable f) :
    HasFiniteIntegral f (μ.Prod ν) ↔
      (∀ᵐ x ∂μ, HasFiniteIntegral (fun y => f (x, y)) ν) ∧
        HasFiniteIntegral (fun x => ∫ y, ‖f (x, y)‖ ∂ν) μ :=
  by
  simp only [has_finite_integral, lintegral_prod_of_measurable _ h1f.ennnorm]
  have : ∀ x, ∀ᵐ y ∂ν, 0 ≤ ‖f (x, y)‖ := fun x => eventually_of_forall fun y => norm_nonneg _
  simp_rw [integral_eq_lintegral_of_nonneg_ae (this _)
      (h1f.norm.comp_measurable measurable_prod_mk_left).AeStronglyMeasurable,
    ennnorm_eq_of_real to_real_nonneg, ofReal_norm_eq_coe_nnnorm]
  -- this fact is probably too specialized to be its own lemma
  have : ∀ {p q r : Prop} (h1 : r → p), (r ↔ p ∧ q) ↔ p → (r ↔ q) := fun p q r h1 => by
    rw [← and_congr_right_iff, and_iff_right_of_imp h1]
  rw [this]
  · intro h2f
    rw [lintegral_congr_ae]
    refine' h2f.mp _
    apply eventually_of_forall
    intro x hx
    dsimp only
    rw [of_real_to_real]
    rw [← lt_top_iff_ne_top]
    exact hx
  · intro h2f
    refine' ae_lt_top _ h2f.ne
    exact h1f.ennnorm.lintegral_prod_right'
#align measure_theory.has_finite_integral_prod_iff MeasureTheory.hasFiniteIntegral_prod_iff

theorem hasFiniteIntegral_prod_iff' ⦃f : α × β → E⦄ (h1f : AeStronglyMeasurable f (μ.Prod ν)) :
    HasFiniteIntegral f (μ.Prod ν) ↔
      (∀ᵐ x ∂μ, HasFiniteIntegral (fun y => f (x, y)) ν) ∧
        HasFiniteIntegral (fun x => ∫ y, ‖f (x, y)‖ ∂ν) μ :=
  by
  rw [has_finite_integral_congr h1f.ae_eq_mk,
    has_finite_integral_prod_iff h1f.strongly_measurable_mk]
  apply and_congr
  · apply eventually_congr
    filter_upwards [ae_ae_of_ae_prod h1f.ae_eq_mk.symm]
    intro x hx
    exact has_finite_integral_congr hx
  · apply has_finite_integral_congr
    filter_upwards [ae_ae_of_ae_prod
        h1f.ae_eq_mk.symm]with _ hx using integral_congr_ae (eventually_eq.fun_comp hx _)
  · infer_instance
#align measure_theory.has_finite_integral_prod_iff' MeasureTheory.hasFiniteIntegral_prod_iff'

/-- A binary function is integrable if the function `y ↦ f (x, y)` is integrable for almost every
  `x` and the function `x ↦ ∫ ‖f (x, y)‖ dy` is integrable. -/
theorem integrable_prod_iff ⦃f : α × β → E⦄ (h1f : AeStronglyMeasurable f (μ.Prod ν)) :
    Integrable f (μ.Prod ν) ↔
      (∀ᵐ x ∂μ, Integrable (fun y => f (x, y)) ν) ∧ Integrable (fun x => ∫ y, ‖f (x, y)‖ ∂ν) μ :=
  by
  simp [integrable, h1f, has_finite_integral_prod_iff', h1f.norm.integral_prod_right',
    h1f.prod_mk_left]
#align measure_theory.integrable_prod_iff MeasureTheory.integrable_prod_iff

/-- A binary function is integrable if the function `x ↦ f (x, y)` is integrable for almost every
  `y` and the function `y ↦ ∫ ‖f (x, y)‖ dx` is integrable. -/
theorem integrable_prod_iff' [SigmaFinite μ] ⦃f : α × β → E⦄
    (h1f : AeStronglyMeasurable f (μ.Prod ν)) :
    Integrable f (μ.Prod ν) ↔
      (∀ᵐ y ∂ν, Integrable (fun x => f (x, y)) μ) ∧ Integrable (fun y => ∫ x, ‖f (x, y)‖ ∂μ) ν :=
  by
  convert integrable_prod_iff h1f.prod_swap using 1
  rw [integrable_swap_iff]
#align measure_theory.integrable_prod_iff' MeasureTheory.integrable_prod_iff'

theorem Integrable.prod_left_ae [SigmaFinite μ] ⦃f : α × β → E⦄ (hf : Integrable f (μ.Prod ν)) :
    ∀ᵐ y ∂ν, Integrable (fun x => f (x, y)) μ :=
  ((integrable_prod_iff' hf.AeStronglyMeasurable).mp hf).1
#align measure_theory.integrable.prod_left_ae MeasureTheory.Integrable.prod_left_ae

theorem Integrable.prod_right_ae [SigmaFinite μ] ⦃f : α × β → E⦄ (hf : Integrable f (μ.Prod ν)) :
    ∀ᵐ x ∂μ, Integrable (fun y => f (x, y)) ν :=
  hf.symm.prod_left_ae
#align measure_theory.integrable.prod_right_ae MeasureTheory.Integrable.prod_right_ae

theorem Integrable.integralNormProdLeft ⦃f : α × β → E⦄ (hf : Integrable f (μ.Prod ν)) :
    Integrable (fun x => ∫ y, ‖f (x, y)‖ ∂ν) μ :=
  ((integrable_prod_iff hf.AeStronglyMeasurable).mp hf).2
#align measure_theory.integrable.integral_norm_prod_left MeasureTheory.Integrable.integralNormProdLeft

theorem Integrable.integralNormProdRight [SigmaFinite μ] ⦃f : α × β → E⦄
    (hf : Integrable f (μ.Prod ν)) : Integrable (fun y => ∫ x, ‖f (x, y)‖ ∂μ) ν :=
  hf.symm.integralNormProdLeft
#align measure_theory.integrable.integral_norm_prod_right MeasureTheory.Integrable.integralNormProdRight

theorem integrableProdMul {L : Type _} [IsROrC L] {f : α → L} {g : β → L} (hf : Integrable f μ)
    (hg : Integrable g ν) : Integrable (fun z : α × β => f z.1 * g z.2) (μ.Prod ν) :=
  by
  refine' (integrable_prod_iff _).2 ⟨_, _⟩
  · exact hf.1.fst.mul hg.1.snd
  · exact eventually_of_forall fun x => hg.const_mul (f x)
  · simpa only [norm_mul, integral_mul_left] using hf.norm.mul_const _
#align measure_theory.integrable_prod_mul MeasureTheory.integrableProdMul

end

variable [NormedSpace ℝ E] [CompleteSpace E]

theorem Integrable.integralProdLeft ⦃f : α × β → E⦄ (hf : Integrable f (μ.Prod ν)) :
    Integrable (fun x => ∫ y, f (x, y) ∂ν) μ :=
  Integrable.mono hf.integralNormProdLeft hf.AeStronglyMeasurable.integral_prod_right' <|
    eventually_of_forall fun x =>
      (norm_integral_le_integral_norm _).trans_eq <|
        (norm_of_nonneg <|
            integral_nonneg_of_ae <|
              eventually_of_forall fun y => (norm_nonneg (f (x, y)) : _)).symm
#align measure_theory.integrable.integral_prod_left MeasureTheory.Integrable.integralProdLeft

theorem Integrable.integralProdRight [SigmaFinite μ] ⦃f : α × β → E⦄
    (hf : Integrable f (μ.Prod ν)) : Integrable (fun y => ∫ x, f (x, y) ∂μ) ν :=
  hf.symm.integral_prod_left
#align measure_theory.integrable.integral_prod_right MeasureTheory.Integrable.integralProdRight

/-! ### The Bochner integral on a product -/


variable [SigmaFinite μ]

theorem integral_prod_swap (f : α × β → E) (hf : AeStronglyMeasurable f (μ.Prod ν)) :
    (∫ z, f z.symm ∂ν.Prod μ) = ∫ z, f z ∂μ.Prod ν :=
  by
  rw [← prod_swap] at hf
  rw [← integral_map measurable_swap.ae_measurable hf, prod_swap]
#align measure_theory.integral_prod_swap MeasureTheory.integral_prod_swap

variable {E' : Type _} [NormedAddCommGroup E'] [CompleteSpace E'] [NormedSpace ℝ E']

/-! Some rules about the sum/difference of double integrals. They follow from `integral_add`, but
  we separate them out as separate lemmas, because they involve quite some steps. -/


/-- Integrals commute with addition inside another integral. `F` can be any function. -/
theorem integral_fn_integral_add ⦃f g : α × β → E⦄ (F : E → E') (hf : Integrable f (μ.Prod ν))
    (hg : Integrable g (μ.Prod ν)) :
    (∫ x, F (∫ y, f (x, y) + g (x, y) ∂ν) ∂μ) = ∫ x, F ((∫ y, f (x, y) ∂ν) + ∫ y, g (x, y) ∂ν) ∂μ :=
  by
  refine' integral_congr_ae _
  filter_upwards [hf.prod_right_ae, hg.prod_right_ae]with _ h2f h2g
  simp [integral_add h2f h2g]
#align measure_theory.integral_fn_integral_add MeasureTheory.integral_fn_integral_add

/-- Integrals commute with subtraction inside another integral.
  `F` can be any measurable function. -/
theorem integral_fn_integral_sub ⦃f g : α × β → E⦄ (F : E → E') (hf : Integrable f (μ.Prod ν))
    (hg : Integrable g (μ.Prod ν)) :
    (∫ x, F (∫ y, f (x, y) - g (x, y) ∂ν) ∂μ) = ∫ x, F ((∫ y, f (x, y) ∂ν) - ∫ y, g (x, y) ∂ν) ∂μ :=
  by
  refine' integral_congr_ae _
  filter_upwards [hf.prod_right_ae, hg.prod_right_ae]with _ h2f h2g
  simp [integral_sub h2f h2g]
#align measure_theory.integral_fn_integral_sub MeasureTheory.integral_fn_integral_sub

/-- Integrals commute with subtraction inside a lower Lebesgue integral.
  `F` can be any function. -/
theorem lintegral_fn_integral_sub ⦃f g : α × β → E⦄ (F : E → ℝ≥0∞) (hf : Integrable f (μ.Prod ν))
    (hg : Integrable g (μ.Prod ν)) :
    (∫⁻ x, F (∫ y, f (x, y) - g (x, y) ∂ν) ∂μ) =
      ∫⁻ x, F ((∫ y, f (x, y) ∂ν) - ∫ y, g (x, y) ∂ν) ∂μ :=
  by
  refine' lintegral_congr_ae _
  filter_upwards [hf.prod_right_ae, hg.prod_right_ae]with _ h2f h2g
  simp [integral_sub h2f h2g]
#align measure_theory.lintegral_fn_integral_sub MeasureTheory.lintegral_fn_integral_sub

/-- Double integrals commute with addition. -/
theorem integral_integral_add ⦃f g : α × β → E⦄ (hf : Integrable f (μ.Prod ν))
    (hg : Integrable g (μ.Prod ν)) :
    (∫ x, ∫ y, f (x, y) + g (x, y) ∂ν ∂μ) = (∫ x, ∫ y, f (x, y) ∂ν ∂μ) + ∫ x, ∫ y, g (x, y) ∂ν ∂μ :=
  (integral_fn_integral_add id hf hg).trans <|
    integral_add hf.integral_prod_left hg.integral_prod_left
#align measure_theory.integral_integral_add MeasureTheory.integral_integral_add

/-- Double integrals commute with addition. This is the version with `(f + g) (x, y)`
  (instead of `f (x, y) + g (x, y)`) in the LHS. -/
theorem integral_integral_add' ⦃f g : α × β → E⦄ (hf : Integrable f (μ.Prod ν))
    (hg : Integrable g (μ.Prod ν)) :
    (∫ x, ∫ y, (f + g) (x, y) ∂ν ∂μ) = (∫ x, ∫ y, f (x, y) ∂ν ∂μ) + ∫ x, ∫ y, g (x, y) ∂ν ∂μ :=
  integral_integral_add hf hg
#align measure_theory.integral_integral_add' MeasureTheory.integral_integral_add'

/-- Double integrals commute with subtraction. -/
theorem integral_integral_sub ⦃f g : α × β → E⦄ (hf : Integrable f (μ.Prod ν))
    (hg : Integrable g (μ.Prod ν)) :
    (∫ x, ∫ y, f (x, y) - g (x, y) ∂ν ∂μ) = (∫ x, ∫ y, f (x, y) ∂ν ∂μ) - ∫ x, ∫ y, g (x, y) ∂ν ∂μ :=
  (integral_fn_integral_sub id hf hg).trans <|
    integral_sub hf.integral_prod_left hg.integral_prod_left
#align measure_theory.integral_integral_sub MeasureTheory.integral_integral_sub

/-- Double integrals commute with subtraction. This is the version with `(f - g) (x, y)`
  (instead of `f (x, y) - g (x, y)`) in the LHS. -/
theorem integral_integral_sub' ⦃f g : α × β → E⦄ (hf : Integrable f (μ.Prod ν))
    (hg : Integrable g (μ.Prod ν)) :
    (∫ x, ∫ y, (f - g) (x, y) ∂ν ∂μ) = (∫ x, ∫ y, f (x, y) ∂ν ∂μ) - ∫ x, ∫ y, g (x, y) ∂ν ∂μ :=
  integral_integral_sub hf hg
#align measure_theory.integral_integral_sub' MeasureTheory.integral_integral_sub'

/-- The map that sends an L¹-function `f : α × β → E` to `∫∫f` is continuous. -/
theorem continuous_integral_integral :
    Continuous fun f : α × β →₁[μ.Prod ν] E => ∫ x, ∫ y, f (x, y) ∂ν ∂μ :=
  by
  rw [continuous_iff_continuousAt]; intro g
  refine'
    tendsto_integral_of_L1 _ (L1.integrable_coe_fn g).integral_prod_left
      (eventually_of_forall fun h => (L1.integrable_coe_fn h).integral_prod_left) _
  simp_rw [←
    lintegral_fn_integral_sub (fun x => (‖x‖₊ : ℝ≥0∞)) (L1.integrable_coe_fn _)
      (L1.integrable_coe_fn g)]
  refine' tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds _ (fun i => zero_le _) _
  · exact fun i => ∫⁻ x, ∫⁻ y, ‖i (x, y) - g (x, y)‖₊ ∂ν ∂μ
  swap; · exact fun i => lintegral_mono fun x => ennnorm_integral_le_lintegral_ennnorm _
  show
    tendsto (fun i : α × β →₁[μ.prod ν] E => ∫⁻ x, ∫⁻ y : β, ‖i (x, y) - g (x, y)‖₊ ∂ν ∂μ) (𝓝 g)
      (𝓝 0)
  have : ∀ i : α × β →₁[μ.prod ν] E, Measurable fun z => (‖i z - g z‖₊ : ℝ≥0∞) := fun i =>
    ((Lp.strongly_measurable i).sub (Lp.strongly_measurable g)).ennnorm
  simp_rw [← lintegral_prod_of_measurable _ (this _), ← L1.of_real_norm_sub_eq_lintegral, ←
    of_real_zero]
  refine' (continuous_of_real.tendsto 0).comp _
  rw [← tendsto_iff_norm_tendsto_zero]; exact tendsto_id
#align measure_theory.continuous_integral_integral MeasureTheory.continuous_integral_integral

/-- **Fubini's Theorem**: For integrable functions on `α × β`,
  the Bochner integral of `f` is equal to the iterated Bochner integral.
  `integrable_prod_iff` can be useful to show that the function in question in integrable.
  `measure_theory.integrable.integral_prod_right` is useful to show that the inner integral
  of the right-hand side is integrable. -/
theorem integral_prod :
    ∀ (f : α × β → E) (hf : Integrable f (μ.Prod ν)),
      (∫ z, f z ∂μ.Prod ν) = ∫ x, ∫ y, f (x, y) ∂ν ∂μ :=
  by
  apply integrable.induction
  · intro c s hs h2s
    simp_rw [integral_indicator hs, ← indicator_comp_right, Function.comp,
      integral_indicator (measurable_prod_mk_left hs), set_integral_const, integral_smul_const,
      integral_to_real (measurable_measure_prod_mk_left hs).AeMeasurable
        (ae_measure_lt_top hs h2s.ne),
      prod_apply hs]
  · intro f g hfg i_f i_g hf hg
    simp_rw [integral_add' i_f i_g, integral_integral_add' i_f i_g, hf, hg]
  · exact isClosed_eq continuous_integral continuous_integral_integral
  · intro f g hfg i_f hf
    convert hf using 1
    · exact integral_congr_ae hfg.symm
    · refine' integral_congr_ae _
      refine' (ae_ae_of_ae_prod hfg).mp _
      apply eventually_of_forall
      intro x hfgx
      exact integral_congr_ae (ae_eq_symm hfgx)
#align measure_theory.integral_prod MeasureTheory.integral_prod

/-- Symmetric version of **Fubini's Theorem**: For integrable functions on `α × β`,
  the Bochner integral of `f` is equal to the iterated Bochner integral.
  This version has the integrals on the right-hand side in the other order. -/
theorem integral_prod_symm (f : α × β → E) (hf : Integrable f (μ.Prod ν)) :
    (∫ z, f z ∂μ.Prod ν) = ∫ y, ∫ x, f (x, y) ∂μ ∂ν :=
  by
  simp_rw [← integral_prod_swap f hf.ae_strongly_measurable]
  exact integral_prod _ hf.swap
#align measure_theory.integral_prod_symm MeasureTheory.integral_prod_symm

/-- Reversed version of **Fubini's Theorem**. -/
theorem integral_integral {f : α → β → E} (hf : Integrable (uncurry f) (μ.Prod ν)) :
    (∫ x, ∫ y, f x y ∂ν ∂μ) = ∫ z, f z.1 z.2 ∂μ.Prod ν :=
  (integral_prod _ hf).symm
#align measure_theory.integral_integral MeasureTheory.integral_integral

/-- Reversed version of **Fubini's Theorem** (symmetric version). -/
theorem integral_integral_symm {f : α → β → E} (hf : Integrable (uncurry f) (μ.Prod ν)) :
    (∫ x, ∫ y, f x y ∂ν ∂μ) = ∫ z, f z.2 z.1 ∂ν.Prod μ :=
  (integral_prod_symm _ hf.symm).symm
#align measure_theory.integral_integral_symm MeasureTheory.integral_integral_symm

/-- Change the order of Bochner integration. -/
theorem integral_integral_swap ⦃f : α → β → E⦄ (hf : Integrable (uncurry f) (μ.Prod ν)) :
    (∫ x, ∫ y, f x y ∂ν ∂μ) = ∫ y, ∫ x, f x y ∂μ ∂ν :=
  (integral_integral hf).trans (integral_prod_symm _ hf)
#align measure_theory.integral_integral_swap MeasureTheory.integral_integral_swap

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/-- **Fubini's Theorem** for set integrals. -/
theorem set_integral_prod (f : α × β → E) {s : Set α} {t : Set β}
    (hf : IntegrableOn f (s ×ˢ t) (μ.Prod ν)) :
    (∫ z in s ×ˢ t, f z ∂μ.Prod ν) = ∫ x in s, ∫ y in t, f (x, y) ∂ν ∂μ :=
  by
  simp only [← measure.prod_restrict s t, integrable_on] at hf⊢
  exact integral_prod f hf
#align measure_theory.set_integral_prod MeasureTheory.set_integral_prod

theorem integral_prod_mul {L : Type _} [IsROrC L] (f : α → L) (g : β → L) :
    (∫ z, f z.1 * g z.2 ∂μ.Prod ν) = (∫ x, f x ∂μ) * ∫ y, g y ∂ν :=
  by
  by_cases h : integrable (fun z : α × β => f z.1 * g z.2) (μ.prod ν)
  · rw [integral_prod _ h]
    simp_rw [integral_mul_left, integral_mul_right]
  have H : ¬integrable f μ ∨ ¬integrable g ν :=
    by
    contrapose! h
    exact integrable_prod_mul h.1 h.2
  cases H <;> simp [integral_undef h, integral_undef H]
#align measure_theory.integral_prod_mul MeasureTheory.integral_prod_mul

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem set_integral_prod_mul {L : Type _} [IsROrC L] (f : α → L) (g : β → L) (s : Set α)
    (t : Set β) :
    (∫ z in s ×ˢ t, f z.1 * g z.2 ∂μ.Prod ν) = (∫ x in s, f x ∂μ) * ∫ y in t, g y ∂ν := by
  simp only [← measure.prod_restrict s t, integrable_on, integral_prod_mul]
#align measure_theory.set_integral_prod_mul MeasureTheory.set_integral_prod_mul

end MeasureTheory

