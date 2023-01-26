/-
Copyright (c) 2021 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel

! This file was ported from Lean 3 source module measure_theory.measure.ae_measurable
! leanprover-community/mathlib commit f93c11933efbc3c2f0299e47b8ff83e9b539cbf6
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.MeasureTheory.Measure.MeasureSpace

/-!
# Almost everywhere measurable functions

A function is almost everywhere measurable if it coincides almost everywhere with a measurable
function. This property, called `ae_measurable f μ`, is defined in the file `measure_space_def`.
We discuss several of its properties that are analogous to properties of measurable functions.
-/


open MeasureTheory MeasureTheory.Measure Filter Set Function

open MeasureTheory Filter Classical Ennreal Interval

variable {ι α β γ δ R : Type _} {m0 : MeasurableSpace α} [MeasurableSpace β] [MeasurableSpace γ]
  [MeasurableSpace δ] {f g : α → β} {μ ν : Measure α}

include m0

section

@[nontriviality, measurability]
theorem Subsingleton.aeMeasurable [Subsingleton α] : AeMeasurable f μ :=
  Subsingleton.measurable.AeMeasurable
#align subsingleton.ae_measurable Subsingleton.aeMeasurable

@[nontriviality, measurability]
theorem aeMeasurableOfSubsingletonCodomain [Subsingleton β] : AeMeasurable f μ :=
  (measurable_of_subsingleton_codomain f).AeMeasurable
#align ae_measurable_of_subsingleton_codomain aeMeasurableOfSubsingletonCodomain

@[simp, measurability]
theorem aeMeasurableZeroMeasure : AeMeasurable f (0 : Measure α) :=
  by
  nontriviality α; inhabit α
  exact ⟨fun x => f default, measurable_const, rfl⟩
#align ae_measurable_zero_measure aeMeasurableZeroMeasure

namespace AeMeasurable

theorem monoMeasure (h : AeMeasurable f μ) (h' : ν ≤ μ) : AeMeasurable f ν :=
  ⟨h.mk f, h.measurable_mk, Eventually.filter_mono (ae_mono h') h.ae_eq_mk⟩
#align ae_measurable.mono_measure AeMeasurable.monoMeasure

theorem monoSet {s t} (h : s ⊆ t) (ht : AeMeasurable f (μ.restrict t)) :
    AeMeasurable f (μ.restrict s) :=
  ht.monoMeasure (restrict_mono h le_rfl)
#align ae_measurable.mono_set AeMeasurable.monoSet

protected theorem mono' (h : AeMeasurable f μ) (h' : ν ≪ μ) : AeMeasurable f ν :=
  ⟨h.mk f, h.measurable_mk, h' h.ae_eq_mk⟩
#align ae_measurable.mono' AeMeasurable.mono'

theorem ae_mem_imp_eq_mk {s} (h : AeMeasurable f (μ.restrict s)) :
    ∀ᵐ x ∂μ, x ∈ s → f x = h.mk f x :=
  ae_imp_of_ae_restrict h.ae_eq_mk
#align ae_measurable.ae_mem_imp_eq_mk AeMeasurable.ae_mem_imp_eq_mk

theorem ae_inf_principal_eq_mk {s} (h : AeMeasurable f (μ.restrict s)) : f =ᶠ[μ.ae ⊓ 𝓟 s] h.mk f :=
  le_ae_restrict h.ae_eq_mk
#align ae_measurable.ae_inf_principal_eq_mk AeMeasurable.ae_inf_principal_eq_mk

@[measurability]
theorem sumMeasure [Countable ι] {μ : ι → Measure α} (h : ∀ i, AeMeasurable f (μ i)) :
    AeMeasurable f (Sum μ) := by
  nontriviality β
  inhabit β
  set s : ι → Set α := fun i => to_measurable (μ i) { x | f x ≠ (h i).mk f x }
  have hsμ : ∀ i, μ i (s i) = 0 := by
    intro i
    rw [measure_to_measurable]
    exact (h i).ae_eq_mk
  have hsm : MeasurableSet (⋂ i, s i) :=
    MeasurableSet.interᵢ fun i => measurable_set_to_measurable _ _
  have hs : ∀ i x, x ∉ s i → f x = (h i).mk f x :=
    by
    intro i x hx
    contrapose! hx
    exact subset_to_measurable _ _ hx
  set g : α → β := (⋂ i, s i).piecewise (const α default) f
  refine' ⟨g, measurable_of_restrict_of_restrict_compl hsm _ _, ae_sum_iff.mpr fun i => _⟩
  · rw [restrict_piecewise]
    simp only [Set.restrict, const]
    exact measurable_const
  · rw [restrict_piecewise_compl, compl_Inter]
    intro t ht
    refine'
      ⟨⋃ i, (h i).mk f ⁻¹' t ∩ s iᶜ,
        MeasurableSet.unionᵢ fun i =>
          (measurable_mk _ ht).inter (measurable_set_to_measurable _ _).compl,
        _⟩
    ext ⟨x, hx⟩
    simp only [mem_preimage, mem_Union, Subtype.coe_mk, Set.restrict, mem_inter_iff,
      mem_compl_iff] at hx⊢
    constructor
    · rintro ⟨i, hxt, hxs⟩
      rwa [hs _ _ hxs]
    · rcases hx with ⟨i, hi⟩
      rw [hs _ _ hi]
      exact fun h => ⟨i, h, hi⟩
  · refine' measure_mono_null (fun x (hx : f x ≠ g x) => _) (hsμ i)
    contrapose! hx
    refine' (piecewise_eq_of_not_mem _ _ _ _).symm
    exact fun h => hx (mem_Inter.1 h i)
#align ae_measurable.sum_measure AeMeasurable.sumMeasure

@[simp]
theorem aeMeasurable_sum_measure_iff [Countable ι] {μ : ι → Measure α} :
    AeMeasurable f (Sum μ) ↔ ∀ i, AeMeasurable f (μ i) :=
  ⟨fun h i => h.monoMeasure (le_sum _ _), sumMeasure⟩
#align ae_measurable_sum_measure_iff aeMeasurable_sum_measure_iff

@[simp]
theorem aeMeasurable_add_measure_iff :
    AeMeasurable f (μ + ν) ↔ AeMeasurable f μ ∧ AeMeasurable f ν :=
  by
  rw [← sum_cond, aeMeasurable_sum_measure_iff, Bool.forall_bool, and_comm]
  rfl
#align ae_measurable_add_measure_iff aeMeasurable_add_measure_iff

@[measurability]
theorem addMeasure {f : α → β} (hμ : AeMeasurable f μ) (hν : AeMeasurable f ν) :
    AeMeasurable f (μ + ν) :=
  aeMeasurable_add_measure_iff.2 ⟨hμ, hν⟩
#align ae_measurable.add_measure AeMeasurable.addMeasure

@[measurability]
protected theorem union [Countable ι] {s : ι → Set α} (h : ∀ i, AeMeasurable f (μ.restrict (s i))) :
    AeMeasurable f (μ.restrict (⋃ i, s i)) :=
  (sumMeasure h).monoMeasure <| restrict_Union_le
#align ae_measurable.Union AeMeasurable.union

@[simp]
theorem aeMeasurable_unionᵢ_iff [Countable ι] {s : ι → Set α} :
    AeMeasurable f (μ.restrict (⋃ i, s i)) ↔ ∀ i, AeMeasurable f (μ.restrict (s i)) :=
  ⟨fun h i => h.monoMeasure <| restrict_mono (subset_unionᵢ _ _) le_rfl, AeMeasurable.union⟩
#align ae_measurable_Union_iff aeMeasurable_unionᵢ_iff

@[simp]
theorem aeMeasurable_union_iff {s t : Set α} :
    AeMeasurable f (μ.restrict (s ∪ t)) ↔
      AeMeasurable f (μ.restrict s) ∧ AeMeasurable f (μ.restrict t) :=
  by simp only [union_eq_Union, aeMeasurable_unionᵢ_iff, Bool.forall_bool, cond, and_comm]
#align ae_measurable_union_iff aeMeasurable_union_iff

@[measurability]
theorem smulMeasure [Monoid R] [DistribMulAction R ℝ≥0∞] [IsScalarTower R ℝ≥0∞ ℝ≥0∞]
    (h : AeMeasurable f μ) (c : R) : AeMeasurable f (c • μ) :=
  ⟨h.mk f, h.measurable_mk, ae_smul_measure h.ae_eq_mk c⟩
#align ae_measurable.smul_measure AeMeasurable.smulMeasure

theorem compAeMeasurable {f : α → δ} {g : δ → β} (hg : AeMeasurable g (μ.map f))
    (hf : AeMeasurable f μ) : AeMeasurable (g ∘ f) μ :=
  ⟨hg.mk g ∘ hf.mk f, hg.measurable_mk.comp hf.measurable_mk,
    (ae_eq_comp hf hg.ae_eq_mk).trans (hf.ae_eq_mk.fun_comp (mk g hg))⟩
#align ae_measurable.comp_ae_measurable AeMeasurable.compAeMeasurable

theorem compMeasurable {f : α → δ} {g : δ → β} (hg : AeMeasurable g (μ.map f)) (hf : Measurable f) :
    AeMeasurable (g ∘ f) μ :=
  hg.compAeMeasurable hf.AeMeasurable
#align ae_measurable.comp_measurable AeMeasurable.compMeasurable

theorem compQuasiMeasurePreserving {ν : Measure δ} {f : α → δ} {g : δ → β} (hg : AeMeasurable g ν)
    (hf : QuasiMeasurePreserving f μ ν) : AeMeasurable (g ∘ f) μ :=
  (hg.mono' hf.AbsolutelyContinuous).compMeasurable hf.Measurable
#align ae_measurable.comp_quasi_measure_preserving AeMeasurable.compQuasiMeasurePreserving

theorem map_map_of_aeMeasurable {g : β → γ} {f : α → β} (hg : AeMeasurable g (Measure.map f μ))
    (hf : AeMeasurable f μ) : (μ.map f).map g = μ.map (g ∘ f) :=
  by
  ext1 s hs
  let g' := hg.mk g
  have A : map g (map f μ) = map g' (map f μ) :=
    by
    apply MeasureTheory.Measure.map_congr
    exact hg.ae_eq_mk
  have B : map (g ∘ f) μ = map (g' ∘ f) μ :=
    by
    apply MeasureTheory.Measure.map_congr
    exact ae_of_ae_map hf hg.ae_eq_mk
  simp only [A, B, hs, hg.measurable_mk.ae_measurable.comp_ae_measurable hf, hg.measurable_mk,
    hg.measurable_mk hs, hf, map_apply, map_apply_of_ae_measurable]
  rfl
#align ae_measurable.map_map_of_ae_measurable AeMeasurable.map_map_of_aeMeasurable

@[measurability]
theorem prodMk {f : α → β} {g : α → γ} (hf : AeMeasurable f μ) (hg : AeMeasurable g μ) :
    AeMeasurable (fun x => (f x, g x)) μ :=
  ⟨fun a => (hf.mk f a, hg.mk g a), hf.measurable_mk.prod_mk hg.measurable_mk,
    EventuallyEq.prod_mk hf.ae_eq_mk hg.ae_eq_mk⟩
#align ae_measurable.prod_mk AeMeasurable.prodMk

theorem exists_ae_eq_range_subset (H : AeMeasurable f μ) {t : Set β} (ht : ∀ᵐ x ∂μ, f x ∈ t)
    (h₀ : t.Nonempty) : ∃ g, Measurable g ∧ range g ⊆ t ∧ f =ᵐ[μ] g :=
  by
  let s : Set α := to_measurable μ ({ x | f x = H.mk f x ∧ f x ∈ t }ᶜ)
  let g : α → β := piecewise s (fun x => h₀.some) (H.mk f)
  refine' ⟨g, _, _, _⟩
  · exact Measurable.piecewise (measurable_set_to_measurable _ _) measurable_const H.measurable_mk
  · rintro _ ⟨x, rfl⟩
    by_cases hx : x ∈ s
    · simpa [g, hx] using h₀.some_mem
    · simp only [g, hx, piecewise_eq_of_not_mem, not_false_iff]
      contrapose! hx
      apply subset_to_measurable
      simp (config := { contextual := true }) only [hx, mem_compl_iff, mem_set_of_eq, not_and,
        not_false_iff, imp_true_iff]
  · have A : μ (to_measurable μ ({ x | f x = H.mk f x ∧ f x ∈ t }ᶜ)) = 0 :=
      by
      rw [measure_to_measurable, ← compl_mem_ae_iff, compl_compl]
      exact H.ae_eq_mk.and ht
    filter_upwards [compl_mem_ae_iff.2 A]with x hx
    rw [mem_compl_iff] at hx
    simp only [g, hx, piecewise_eq_of_not_mem, not_false_iff]
    contrapose! hx
    apply subset_to_measurable
    simp only [hx, mem_compl_iff, mem_set_of_eq, false_and_iff, not_false_iff]
#align ae_measurable.exists_ae_eq_range_subset AeMeasurable.exists_ae_eq_range_subset

theorem exists_measurable_nonneg {β} [Preorder β] [Zero β] {mβ : MeasurableSpace β} {f : α → β}
    (hf : AeMeasurable f μ) (f_nn : ∀ᵐ t ∂μ, 0 ≤ f t) : ∃ g, Measurable g ∧ 0 ≤ g ∧ f =ᵐ[μ] g :=
  by
  obtain ⟨G, hG_meas, hG_mem, hG_ae_eq⟩ := hf.exists_ae_eq_range_subset f_nn ⟨0, le_rfl⟩
  exact ⟨G, hG_meas, fun x => hG_mem (mem_range_self x), hG_ae_eq⟩
#align ae_measurable.exists_measurable_nonneg AeMeasurable.exists_measurable_nonneg

theorem subtypeMk (h : AeMeasurable f μ) {s : Set β} {hfs : ∀ x, f x ∈ s} :
    AeMeasurable (codRestrict f s hfs) μ :=
  by
  nontriviality α; inhabit α
  obtain ⟨g, g_meas, hg, fg⟩ : ∃ g : α → β, Measurable g ∧ range g ⊆ s ∧ f =ᵐ[μ] g :=
    h.exists_ae_eq_range_subset (eventually_of_forall hfs) ⟨_, hfs default⟩
  refine' ⟨cod_restrict g s fun x => hg (mem_range_self _), Measurable.subtype_mk g_meas, _⟩
  filter_upwards [fg]with x hx
  simpa [Subtype.ext_iff]
#align ae_measurable.subtype_mk AeMeasurable.subtypeMk

protected theorem nullMeasurable (h : AeMeasurable f μ) : NullMeasurable f μ :=
  let ⟨g, hgm, hg⟩ := h
  hgm.NullMeasurable.congr hg.symm
#align ae_measurable.null_measurable AeMeasurable.nullMeasurable

end AeMeasurable

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (x y) -/
theorem aeMeasurableConst' (h : ∀ᵐ (x) (y) ∂μ, f x = f y) : AeMeasurable f μ :=
  by
  rcases eq_or_ne μ 0 with (rfl | hμ)
  · exact aeMeasurableZeroMeasure
  · haveI := ae_ne_bot.2 hμ
    rcases h.exists with ⟨x, hx⟩
    exact ⟨const α (f x), measurable_const, eventually_eq.symm hx⟩
#align ae_measurable_const' aeMeasurableConst'

theorem aeMeasurable_uIoc_iff [LinearOrder α] {f : α → β} {a b : α} :
    (AeMeasurable f <| μ.restrict <| Ι a b) ↔
      (AeMeasurable f <| μ.restrict <| Ioc a b) ∧ (AeMeasurable f <| μ.restrict <| Ioc b a) :=
  by rw [uIoc_eq_union, aeMeasurable_union_iff]
#align ae_measurable_uIoc_iff aeMeasurable_uIoc_iff

theorem aeMeasurable_iff_measurable [μ.IsComplete] : AeMeasurable f μ ↔ Measurable f :=
  ⟨fun h => h.NullMeasurable.measurable_of_complete, fun h => h.AeMeasurable⟩
#align ae_measurable_iff_measurable aeMeasurable_iff_measurable

theorem MeasurableEmbedding.aeMeasurable_map_iff {g : β → γ} (hf : MeasurableEmbedding f) :
    AeMeasurable g (μ.map f) ↔ AeMeasurable (g ∘ f) μ :=
  by
  refine' ⟨fun H => H.compMeasurable hf.measurable, _⟩
  rintro ⟨g₁, hgm₁, heq⟩
  rcases hf.exists_measurable_extend hgm₁ fun x => ⟨g x⟩ with ⟨g₂, hgm₂, rfl⟩
  exact ⟨g₂, hgm₂, hf.ae_map_iff.2 HEq⟩
#align measurable_embedding.ae_measurable_map_iff MeasurableEmbedding.aeMeasurable_map_iff

theorem MeasurableEmbedding.aeMeasurable_comp_iff {g : β → γ} (hg : MeasurableEmbedding g)
    {μ : Measure α} : AeMeasurable (g ∘ f) μ ↔ AeMeasurable f μ :=
  by
  refine' ⟨fun H => _, hg.measurable.comp_ae_measurable⟩
  suffices AeMeasurable ((range_splitting g ∘ range_factorization g) ∘ f) μ by
    rwa [(right_inverse_range_splitting hg.injective).comp_eq_id] at this
  exact hg.measurable_range_splitting.comp_ae_measurable H.subtype_mk
#align measurable_embedding.ae_measurable_comp_iff MeasurableEmbedding.aeMeasurable_comp_iff

theorem aeMeasurable_restrict_iff_comap_subtype {s : Set α} (hs : MeasurableSet s) {μ : Measure α}
    {f : α → β} : AeMeasurable f (μ.restrict s) ↔ AeMeasurable (f ∘ coe : s → β) (comap coe μ) := by
  rw [← map_comap_subtype_coe hs, (MeasurableEmbedding.subtype_coe hs).ae_measurable_map_iff]
#align ae_measurable_restrict_iff_comap_subtype aeMeasurable_restrict_iff_comap_subtype

@[simp, to_additive]
theorem aeMeasurableOne [One β] : AeMeasurable (fun a : α => (1 : β)) μ :=
  measurable_one.AeMeasurable
#align ae_measurable_one aeMeasurableOne
#align ae_measurable_zero ae_measurable_zero

@[simp]
theorem aeMeasurable_smul_measure_iff {c : ℝ≥0∞} (hc : c ≠ 0) :
    AeMeasurable f (c • μ) ↔ AeMeasurable f μ :=
  ⟨fun h => ⟨h.mk f, h.measurable_mk, (ae_smul_measure_iff hc).1 h.ae_eq_mk⟩, fun h =>
    ⟨h.mk f, h.measurable_mk, (ae_smul_measure_iff hc).2 h.ae_eq_mk⟩⟩
#align ae_measurable_smul_measure_iff aeMeasurable_smul_measure_iff

theorem aeMeasurableOfAeMeasurableTrim {α} {m m0 : MeasurableSpace α} {μ : Measure α} (hm : m ≤ m0)
    {f : α → β} (hf : AeMeasurable f (μ.trim hm)) : AeMeasurable f μ :=
  ⟨hf.mk f, Measurable.mono hf.measurable_mk hm le_rfl, ae_eq_of_ae_eq_trim hf.ae_eq_mk⟩
#align ae_measurable_of_ae_measurable_trim aeMeasurableOfAeMeasurableTrim

theorem aeMeasurableRestrictOfMeasurableSubtype {s : Set α} (hs : MeasurableSet s)
    (hf : Measurable fun x : s => f x) : AeMeasurable f (μ.restrict s) :=
  (aeMeasurable_restrict_iff_comap_subtype hs).2 hf.AeMeasurable
#align ae_measurable_restrict_of_measurable_subtype aeMeasurableRestrictOfMeasurableSubtype

theorem aeMeasurable_map_equiv_iff (e : α ≃ᵐ β) {f : β → γ} :
    AeMeasurable f (μ.map e) ↔ AeMeasurable (f ∘ e) μ :=
  e.MeasurableEmbedding.ae_measurable_map_iff
#align ae_measurable_map_equiv_iff aeMeasurable_map_equiv_iff

end

theorem AeMeasurable.restrict (hfm : AeMeasurable f μ) {s} : AeMeasurable f (μ.restrict s) :=
  ⟨AeMeasurable.mk f hfm, hfm.measurable_mk, ae_restrict_of_ae hfm.ae_eq_mk⟩
#align ae_measurable.restrict AeMeasurable.restrict

theorem aeMeasurableIoiOfForallIoc {β} {mβ : MeasurableSpace β} [LinearOrder α]
    [(atTop : Filter α).IsCountablyGenerated] {x : α} {g : α → β}
    (g_meas : ∀ t > x, AeMeasurable g (μ.restrict (Ioc x t))) :
    AeMeasurable g (μ.restrict (Ioi x)) :=
  by
  haveI : Nonempty α := ⟨x⟩
  obtain ⟨u, hu_tendsto⟩ := exists_seq_tendsto (at_top : Filter α)
  have Ioi_eq_Union : Ioi x = ⋃ n : ℕ, Ioc x (u n) :=
    by
    rw [Union_Ioc_eq_Ioi_self_iff.mpr _]
    exact fun y _ => (hu_tendsto.eventually (eventually_ge_at_top y)).exists
  rw [Ioi_eq_Union, aeMeasurable_unionᵢ_iff]
  intro n
  cases lt_or_le x (u n)
  · exact g_meas (u n) h
  · rw [Ioc_eq_empty (not_lt.mpr h), measure.restrict_empty]
    exact aeMeasurableZeroMeasure
#align ae_measurable_Ioi_of_forall_Ioc aeMeasurableIoiOfForallIoc

variable [Zero β]

theorem aeMeasurable_indicator_iff {s} (hs : MeasurableSet s) :
    AeMeasurable (indicator s f) μ ↔ AeMeasurable f (μ.restrict s) :=
  by
  constructor
  · intro h
    exact (h.mono_measure measure.restrict_le_self).congr (indicator_ae_eq_restrict hs)
  · intro h
    refine' ⟨indicator s (h.mk f), h.measurable_mk.indicator hs, _⟩
    have A : s.indicator f =ᵐ[μ.restrict s] s.indicator (AeMeasurable.mk f h) :=
      (indicator_ae_eq_restrict hs).trans (h.ae_eq_mk.trans <| (indicator_ae_eq_restrict hs).symm)
    have B : s.indicator f =ᵐ[μ.restrict (sᶜ)] s.indicator (AeMeasurable.mk f h) :=
      (indicator_ae_eq_restrict_compl hs).trans (indicator_ae_eq_restrict_compl hs).symm
    exact ae_of_ae_restrict_of_ae_restrict_compl _ A B
#align ae_measurable_indicator_iff aeMeasurable_indicator_iff

@[measurability]
theorem AeMeasurable.indicator (hfm : AeMeasurable f μ) {s} (hs : MeasurableSet s) :
    AeMeasurable (s.indicator f) μ :=
  (aeMeasurable_indicator_iff hs).mpr hfm.restrict
#align ae_measurable.indicator AeMeasurable.indicator

theorem MeasureTheory.Measure.restrict_map_of_aeMeasurable {f : α → δ} (hf : AeMeasurable f μ)
    {s : Set δ} (hs : MeasurableSet s) : (μ.map f).restrict s = (μ.restrict <| f ⁻¹' s).map f :=
  calc
    (μ.map f).restrict s = (μ.map (hf.mk f)).restrict s :=
      by
      congr 1
      apply measure.map_congr hf.ae_eq_mk
    _ = (μ.restrict <| hf.mk f ⁻¹' s).map (hf.mk f) := Measure.restrict_map hf.measurable_mk hs
    _ = (μ.restrict <| hf.mk f ⁻¹' s).map f :=
      Measure.map_congr (ae_restrict_of_ae hf.ae_eq_mk.symm)
    _ = (μ.restrict <| f ⁻¹' s).map f := by
      apply congr_arg
      ext1 t ht
      simp only [ht, measure.restrict_apply]
      apply measure_congr
      apply (eventually_eq.refl _ _).inter (hf.ae_eq_mk.symm.preimage s)
    
#align measure_theory.measure.restrict_map_of_ae_measurable MeasureTheory.Measure.restrict_map_of_aeMeasurable

theorem MeasureTheory.Measure.map_mono_of_aeMeasurable {f : α → δ} (h : μ ≤ ν)
    (hf : AeMeasurable f ν) : μ.map f ≤ ν.map f := fun s hs => by
  simpa [hf, hs, hf.mono_measure h] using measure.le_iff'.1 h (f ⁻¹' s)
#align measure_theory.measure.map_mono_of_ae_measurable MeasureTheory.Measure.map_mono_of_aeMeasurable

