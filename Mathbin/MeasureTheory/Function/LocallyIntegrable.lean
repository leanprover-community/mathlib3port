/-
Copyright (c) 2022 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn

! This file was ported from Lean 3 source module measure_theory.function.locally_integrable
! leanprover-community/mathlib commit dde670c9a3f503647fd5bfdf1037bad526d3397a
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.MeasureTheory.Integral.IntegrableOn

/-!
# Locally integrable functions

A function is called *locally integrable* (`measure_theory.locally_integrable`) if it is integrable
on a neighborhood of every point.

This file contains properties of locally integrable functions and integrability results
on compact sets.

## Main statements

* `continuous.locally_integrable`: A continuous function is locally integrable.

-/


open MeasureTheory MeasureTheory.Measure Set Function TopologicalSpace

open Topology Interval

variable {X Y E R : Type _} [MeasurableSpace X] [TopologicalSpace X]

variable [MeasurableSpace Y] [TopologicalSpace Y]

variable [NormedAddCommGroup E] {f : X → E} {μ : Measure X}

namespace MeasureTheory

/-- A function `f : X → E` is locally integrable if it is integrable on a neighborhood of every
point. In particular, it is integrable on all compact sets,
see `locally_integrable.integrable_on_is_compact`. -/
def LocallyIntegrable (f : X → E) (μ : Measure X := by exact MeasureTheory.MeasureSpace.volume) :
    Prop :=
  ∀ x : X, IntegrableAtFilter f (𝓝 x) μ
#align measure_theory.locally_integrable MeasureTheory.LocallyIntegrable

theorem Integrable.locallyIntegrable (hf : Integrable f μ) : LocallyIntegrable f μ := fun x =>
  hf.IntegrableAtFilter _
#align measure_theory.integrable.locally_integrable MeasureTheory.Integrable.locallyIntegrable

/-- If a function is locally integrable, then it is integrable on an open neighborhood of any
compact set. -/
theorem LocallyIntegrable.integrableOn_nhds_isCompact (hf : LocallyIntegrable f μ) {k : Set X}
    (hk : IsCompact k) : ∃ u, IsOpen u ∧ k ⊆ u ∧ IntegrableOn f u μ :=
  by
  refine' IsCompact.induction_on hk _ _ _ _
  · refine' ⟨∅, isOpen_empty, subset.rfl, integrable_on_empty⟩
  · rintro s t hst ⟨u, u_open, tu, hu⟩
    exact ⟨u, u_open, hst.trans tu, hu⟩
  · rintro s t ⟨u, u_open, su, hu⟩ ⟨v, v_open, tv, hv⟩
    exact ⟨u ∪ v, u_open.union v_open, union_subset_union su tv, hu.union hv⟩
  · intro x hx
    rcases hf x with ⟨u, ux, hu⟩
    rcases mem_nhds_iff.1 ux with ⟨v, vu, v_open, xv⟩
    exact ⟨v, nhdsWithin_le_nhds (v_open.mem_nhds xv), v, v_open, subset.rfl, hu.mono_set vu⟩
#align measure_theory.locally_integrable.integrable_on_nhds_is_compact MeasureTheory.LocallyIntegrable.integrableOn_nhds_isCompact

/-- If a function is locally integrable, then it is integrable on any compact set. -/
theorem LocallyIntegrable.integrableOnIsCompact {k : Set X} (hf : LocallyIntegrable f μ)
    (hk : IsCompact k) : IntegrableOn f k μ :=
  by
  rcases hf.integrable_on_nhds_is_compact hk with ⟨u, u_open, ku, hu⟩
  exact hu.mono_set ku
#align measure_theory.locally_integrable.integrable_on_is_compact MeasureTheory.LocallyIntegrable.integrableOnIsCompact

theorem locallyIntegrable_iff [LocallyCompactSpace X] :
    LocallyIntegrable f μ ↔ ∀ k : Set X, IsCompact k → IntegrableOn f k μ :=
  by
  refine' ⟨fun hf k hk => hf.integrableOnIsCompact hk, fun hf x => _⟩
  obtain ⟨K, hK, h2K⟩ := exists_compact_mem_nhds x
  exact ⟨K, h2K, hf K hK⟩
#align measure_theory.locally_integrable_iff MeasureTheory.locallyIntegrable_iff

theorem LocallyIntegrable.aeStronglyMeasurable [SecondCountableTopology X]
    (hf : LocallyIntegrable f μ) : AeStronglyMeasurable f μ :=
  by
  have : ∀ x, ∃ u, IsOpen u ∧ x ∈ u ∧ integrable_on f u μ :=
    by
    intro x
    rcases hf x with ⟨s, hs, h's⟩
    rcases mem_nhds_iff.1 hs with ⟨u, us, u_open, xu⟩
    exact ⟨u, u_open, xu, h's.mono_set us⟩
  choose u u_open xu hu using this
  obtain ⟨T, T_count, hT⟩ : ∃ T : Set X, T.Countable ∧ (⋃ i : T, u i) = univ :=
    by
    have : (⋃ x, u x) = univ := eq_univ_of_forall fun x => mem_Union_of_mem x (xu x)
    rw [← this]
    simp only [Union_coe_set, Subtype.coe_mk]
    exact is_open_Union_countable u u_open
  have : Countable T := countable_coe_iff.mpr T_count
  rw [← @restrict_univ _ _ μ, ← hT, aeStronglyMeasurable_unionᵢ_iff]
  exact fun i => (hu i).AeStronglyMeasurable
#align measure_theory.locally_integrable.ae_strongly_measurable MeasureTheory.LocallyIntegrable.aeStronglyMeasurable

theorem locallyIntegrableConst [IsLocallyFiniteMeasure μ] (c : E) :
    LocallyIntegrable (fun x => c) μ := by
  intro x
  rcases μ.finite_at_nhds x with ⟨U, hU, h'U⟩
  refine' ⟨U, hU, _⟩
  simp only [h'U, integrable_on_const, or_true_iff]
#align measure_theory.locally_integrable_const MeasureTheory.locallyIntegrableConst

theorem LocallyIntegrable.indicator (hf : LocallyIntegrable f μ) {s : Set X}
    (hs : MeasurableSet s) : LocallyIntegrable (s.indicator f) μ :=
  by
  intro x
  rcases hf x with ⟨U, hU, h'U⟩
  exact ⟨U, hU, h'U.indicator hs⟩
#align measure_theory.locally_integrable.indicator MeasureTheory.LocallyIntegrable.indicator

theorem locallyIntegrable_map_homeomorph [BorelSpace X] [BorelSpace Y] (e : X ≃ₜ Y) {f : Y → E}
    {μ : Measure X} : LocallyIntegrable f (Measure.map e μ) ↔ LocallyIntegrable (f ∘ e) μ :=
  by
  refine' ⟨fun h x => _, fun h x => _⟩
  · rcases h (e x) with ⟨U, hU, h'U⟩
    refine' ⟨e ⁻¹' U, e.continuous.continuous_at.preimage_mem_nhds hU, _⟩
    exact (integrable_on_map_equiv e.to_measurable_equiv).1 h'U
  · rcases h (e.symm x) with ⟨U, hU, h'U⟩
    refine' ⟨e.symm ⁻¹' U, e.symm.continuous.continuous_at.preimage_mem_nhds hU, _⟩
    apply (integrable_on_map_equiv e.to_measurable_equiv).2
    simp only [Homeomorph.toMeasurableEquiv_coe]
    convert h'U
    ext x
    simp only [mem_preimage, Homeomorph.symm_apply_apply]
#align measure_theory.locally_integrable_map_homeomorph MeasureTheory.locallyIntegrable_map_homeomorph

section Mul

variable [OpensMeasurableSpace X] [NormedRing R] [SecondCountableTopologyEither X R] {A K : Set X}
  {g g' : X → R}

theorem IntegrableOn.mulContinuousOnOfSubset (hg : IntegrableOn g A μ) (hg' : ContinuousOn g' K)
    (hA : MeasurableSet A) (hK : IsCompact K) (hAK : A ⊆ K) :
    IntegrableOn (fun x => g x * g' x) A μ :=
  by
  rcases IsCompact.exists_bound_of_continuousOn hK hg' with ⟨C, hC⟩
  rw [integrable_on, ← mem_ℒp_one_iff_integrable] at hg⊢
  have : ∀ᵐ x ∂μ.restrict A, ‖g x * g' x‖ ≤ C * ‖g x‖ :=
    by
    filter_upwards [ae_restrict_mem hA]with x hx
    refine' (norm_mul_le _ _).trans _
    rw [mul_comm]
    apply mul_le_mul_of_nonneg_right (hC x (hAK hx)) (norm_nonneg _)
  exact
    mem_ℒp.of_le_mul hg (hg.ae_strongly_measurable.mul <| (hg'.mono hAK).AeStronglyMeasurable hA)
      this
#align measure_theory.integrable_on.mul_continuous_on_of_subset MeasureTheory.IntegrableOn.mulContinuousOnOfSubset

theorem IntegrableOn.mulContinuousOn [T2Space X] (hg : IntegrableOn g K μ) (hg' : ContinuousOn g' K)
    (hK : IsCompact K) : IntegrableOn (fun x => g x * g' x) K μ :=
  hg.mulContinuousOnOfSubset hg' hK.MeasurableSet hK (Subset.refl _)
#align measure_theory.integrable_on.mul_continuous_on MeasureTheory.IntegrableOn.mulContinuousOn

theorem IntegrableOn.continuousOnMulOfSubset (hg : ContinuousOn g K) (hg' : IntegrableOn g' A μ)
    (hK : IsCompact K) (hA : MeasurableSet A) (hAK : A ⊆ K) :
    IntegrableOn (fun x => g x * g' x) A μ :=
  by
  rcases IsCompact.exists_bound_of_continuousOn hK hg with ⟨C, hC⟩
  rw [integrable_on, ← mem_ℒp_one_iff_integrable] at hg'⊢
  have : ∀ᵐ x ∂μ.restrict A, ‖g x * g' x‖ ≤ C * ‖g' x‖ :=
    by
    filter_upwards [ae_restrict_mem hA]with x hx
    refine' (norm_mul_le _ _).trans _
    apply mul_le_mul_of_nonneg_right (hC x (hAK hx)) (norm_nonneg _)
  exact
    mem_ℒp.of_le_mul hg' (((hg.mono hAK).AeStronglyMeasurable hA).mul hg'.ae_strongly_measurable)
      this
#align measure_theory.integrable_on.continuous_on_mul_of_subset MeasureTheory.IntegrableOn.continuousOnMulOfSubset

theorem IntegrableOn.continuousOnMul [T2Space X] (hg : ContinuousOn g K) (hg' : IntegrableOn g' K μ)
    (hK : IsCompact K) : IntegrableOn (fun x => g x * g' x) K μ :=
  hg'.continuousOnMulOfSubset hg hK hK.MeasurableSet Subset.rfl
#align measure_theory.integrable_on.continuous_on_mul MeasureTheory.IntegrableOn.continuousOnMul

end Mul

end MeasureTheory

open MeasureTheory

/-- If a function is integrable at `𝓝[s] x` for each point `x` of a compact set `s`, then it is
integrable on `s`. -/
theorem IsCompact.integrableOnOfNhdsWithin {K : Set X} (hK : IsCompact K)
    (hf : ∀ x ∈ K, IntegrableAtFilter f (𝓝[K] x) μ) : IntegrableOn f K μ :=
  IsCompact.induction_on hK integrableOnEmpty (fun s t hst ht => ht.monoSet hst)
    (fun s t hs ht => hs.union ht) hf
#align is_compact.integrable_on_of_nhds_within IsCompact.integrableOnOfNhdsWithin

section borel

variable [OpensMeasurableSpace X] [IsLocallyFiniteMeasure μ]

variable {K : Set X} {a b : X}

/-- A continuous function `f` is locally integrable with respect to any locally finite measure. -/
theorem Continuous.locallyIntegrable [SecondCountableTopologyEither X E] (hf : Continuous f) :
    LocallyIntegrable f μ :=
  hf.integrableAtNhds
#align continuous.locally_integrable Continuous.locallyIntegrable

variable [MetrizableSpace X]

/-- A function `f` continuous on a compact set `K` is integrable on this set with respect to any
locally finite measure. -/
theorem ContinuousOn.integrableOnCompact (hK : IsCompact K) (hf : ContinuousOn f K) :
    IntegrableOn f K μ := by
  letI := metrizable_space_metric X
  apply hK.integrable_on_of_nhds_within fun x hx => _
  exact hf.integrable_at_nhds_within_of_is_separable hK.measurable_set hK.is_separable hx
#align continuous_on.integrable_on_compact ContinuousOn.integrableOnCompact

theorem ContinuousOn.integrableOnIcc [Preorder X] [CompactIccSpace X]
    (hf : ContinuousOn f (Icc a b)) : IntegrableOn f (Icc a b) μ :=
  hf.integrableOnCompact isCompact_Icc
#align continuous_on.integrable_on_Icc ContinuousOn.integrableOnIcc

theorem Continuous.integrableOnIcc [Preorder X] [CompactIccSpace X] (hf : Continuous f) :
    IntegrableOn f (Icc a b) μ :=
  hf.ContinuousOn.integrableOnIcc
#align continuous.integrable_on_Icc Continuous.integrableOnIcc

theorem Continuous.integrableOnIoc [Preorder X] [CompactIccSpace X] (hf : Continuous f) :
    IntegrableOn f (Ioc a b) μ :=
  hf.integrableOnIcc.monoSet Ioc_subset_Icc_self
#align continuous.integrable_on_Ioc Continuous.integrableOnIoc

theorem ContinuousOn.integrableOnUIcc [LinearOrder X] [CompactIccSpace X]
    (hf : ContinuousOn f [a, b]) : IntegrableOn f [a, b] μ :=
  hf.integrableOnIcc
#align continuous_on.integrable_on_uIcc ContinuousOn.integrableOnUIcc

theorem Continuous.integrableOnUIcc [LinearOrder X] [CompactIccSpace X] (hf : Continuous f) :
    IntegrableOn f [a, b] μ :=
  hf.integrableOnIcc
#align continuous.integrable_on_uIcc Continuous.integrableOnUIcc

theorem Continuous.integrableOnUIoc [LinearOrder X] [CompactIccSpace X] (hf : Continuous f) :
    IntegrableOn f (Ι a b) μ :=
  hf.integrableOnIoc
#align continuous.integrable_on_uIoc Continuous.integrableOnUIoc

/-- A continuous function with compact support is integrable on the whole space. -/
theorem Continuous.integrableOfHasCompactSupport (hf : Continuous f) (hcf : HasCompactSupport f) :
    Integrable f μ :=
  (integrableOn_iff_integrable_of_support_subset (subset_tsupport f)).mp <|
    hf.ContinuousOn.integrableOnCompact hcf
#align continuous.integrable_of_has_compact_support Continuous.integrableOfHasCompactSupport

end borel

open Ennreal

section Monotone

variable [BorelSpace X] [ConditionallyCompleteLinearOrder X] [ConditionallyCompleteLinearOrder E]
  [OrderTopology X] [OrderTopology E] [SecondCountableTopology E] {s : Set X}

theorem MonotoneOn.integrableOnOfMeasureNeTop (hmono : MonotoneOn f s) {a b : X} (ha : IsLeast s a)
    (hb : IsGreatest s b) (hs : μ s ≠ ∞) (h's : MeasurableSet s) : IntegrableOn f s μ :=
  by
  borelize E
  obtain rfl | h := s.eq_empty_or_nonempty
  · exact integrable_on_empty
  have hbelow : BddBelow (f '' s) := ⟨f a, fun x ⟨y, hy, hyx⟩ => hyx ▸ hmono ha.1 hy (ha.2 hy)⟩
  have habove : BddAbove (f '' s) := ⟨f b, fun x ⟨y, hy, hyx⟩ => hyx ▸ hmono hy hb.1 (hb.2 hy)⟩
  have : Metric.Bounded (f '' s) := Metric.bounded_of_bddAbove_of_bddBelow habove hbelow
  rcases bounded_iff_forall_norm_le.mp this with ⟨C, hC⟩
  have A : integrable_on (fun x => C) s μ := by
    simp only [hs.lt_top, integrable_on_const, or_true_iff]
  refine'
    integrable.mono' A (aeMeasurableRestrictOfMonotoneOn h's hmono).AeStronglyMeasurable
      ((ae_restrict_iff' h's).mpr <| ae_of_all _ fun y hy => hC (f y) (mem_image_of_mem f hy))
#align monotone_on.integrable_on_of_measure_ne_top MonotoneOn.integrableOnOfMeasureNeTop

theorem MonotoneOn.integrableOnIsCompact [IsFiniteMeasureOnCompacts μ] (hs : IsCompact s)
    (hmono : MonotoneOn f s) : IntegrableOn f s μ :=
  by
  obtain rfl | h := s.eq_empty_or_nonempty
  · exact integrable_on_empty
  ·
    exact
      hmono.integrable_on_of_measure_ne_top (hs.is_least_Inf h) (hs.is_greatest_Sup h)
        hs.measure_lt_top.ne hs.measurable_set
#align monotone_on.integrable_on_is_compact MonotoneOn.integrableOnIsCompact

theorem AntitoneOn.integrableOnOfMeasureNeTop (hanti : AntitoneOn f s) {a b : X} (ha : IsLeast s a)
    (hb : IsGreatest s b) (hs : μ s ≠ ∞) (h's : MeasurableSet s) : IntegrableOn f s μ :=
  hanti.dual_right.integrableOnOfMeasureNeTop ha hb hs h's
#align antitone_on.integrable_on_of_measure_ne_top AntitoneOn.integrableOnOfMeasureNeTop

theorem AntioneOn.integrableOnIsCompact [IsFiniteMeasureOnCompacts μ] (hs : IsCompact s)
    (hanti : AntitoneOn f s) : IntegrableOn f s μ :=
  hanti.dual_right.integrableOnIsCompact hs
#align antione_on.integrable_on_is_compact AntioneOn.integrableOnIsCompact

theorem Monotone.locallyIntegrable [IsLocallyFiniteMeasure μ] (hmono : Monotone f) :
    LocallyIntegrable f μ := by
  intro x
  rcases μ.finite_at_nhds x with ⟨U, hU, h'U⟩
  obtain ⟨a, b, xab, hab, abU⟩ : ∃ a b : X, x ∈ Icc a b ∧ Icc a b ∈ 𝓝 x ∧ Icc a b ⊆ U
  exact exists_Icc_mem_subset_of_mem_nhds hU
  have ab : a ≤ b := xab.1.trans xab.2
  refine' ⟨Icc a b, hab, _⟩
  exact
    (hmono.monotone_on _).integrableOnOfMeasureNeTop (isLeast_Icc ab) (isGreatest_Icc ab)
      ((measure_mono abU).trans_lt h'U).Ne measurableSet_Icc
#align monotone.locally_integrable Monotone.locallyIntegrable

theorem Antitone.locallyIntegrable [IsLocallyFiniteMeasure μ] (hanti : Antitone f) :
    LocallyIntegrable f μ :=
  hanti.dual_right.LocallyIntegrable
#align antitone.locally_integrable Antitone.locallyIntegrable

end Monotone

