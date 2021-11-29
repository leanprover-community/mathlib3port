import Mathbin.MeasureTheory.Function.L1Space 
import Mathbin.Analysis.NormedSpace.IndicatorFunction

/-! # Functions integrable on a set and at a filter

We define `integrable_on f s μ := integrable f (μ.restrict s)` and prove theorems like
`integrable_on_union : integrable_on f (s ∪ t) μ ↔ integrable_on f s μ ∧ integrable_on f t μ`.

Next we define a predicate `integrable_at_filter (f : α → E) (l : filter α) (μ : measure α)`
saying that `f` is integrable at some set `s ∈ l` and prove that a measurable function is integrable
at `l` with respect to `μ` provided that `f` is bounded above at `l ⊓ μ.ae` and `μ` is finite
at `l`.

-/


noncomputable theory

open Set Filter TopologicalSpace MeasureTheory Function

open_locale Classical TopologicalSpace Interval BigOperators Filter Ennreal MeasureTheory

variable {α β E F : Type _} [MeasurableSpace α]

section 

variable [MeasurableSpace β] {l l' : Filter α} {f g : α → β} {μ ν : Measureₓ α}

/-- A function `f` is measurable at filter `l` w.r.t. a measure `μ` if it is ae-measurable
w.r.t. `μ.restrict s` for some `s ∈ l`. -/
def MeasurableAtFilter (f : α → β) (l : Filter α)
  (μ : Measureₓ α :=  by 
    runTac 
      volume_tac) :=
  ∃ (s : _)(_ : s ∈ l), AeMeasurable f (μ.restrict s)

@[simp]
theorem measurable_at_bot {f : α → β} : MeasurableAtFilter f ⊥ μ :=
  ⟨∅, mem_bot,
    by 
      simp ⟩

protected theorem MeasurableAtFilter.eventually (h : MeasurableAtFilter f l μ) :
  ∀ᶠs in l.lift' powerset, AeMeasurable f (μ.restrict s) :=
  (eventually_lift'_powerset'$ fun s t => AeMeasurable.mono_set).2 h

protected theorem MeasurableAtFilter.filter_mono (h : MeasurableAtFilter f l μ) (h' : l' ≤ l) :
  MeasurableAtFilter f l' μ :=
  let ⟨s, hsl, hs⟩ := h
  ⟨s, h' hsl, hs⟩

protected theorem AeMeasurable.measurable_at_filter (h : AeMeasurable f μ) : MeasurableAtFilter f l μ :=
  ⟨univ, univ_mem,
    by 
      rwa [measure.restrict_univ]⟩

theorem AeMeasurable.measurable_at_filter_of_mem {s} (h : AeMeasurable f (μ.restrict s)) (hl : s ∈ l) :
  MeasurableAtFilter f l μ :=
  ⟨s, hl, h⟩

protected theorem Measurable.measurable_at_filter (h : Measurable f) : MeasurableAtFilter f l μ :=
  h.ae_measurable.measurable_at_filter

end 

namespace MeasureTheory

section NormedGroup

-- error in MeasureTheory.Integral.IntegrableOn: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem has_finite_integral_restrict_of_bounded
[normed_group E]
{f : α → E}
{s : set α}
{μ : measure α}
{C}
(hs : «expr < »(μ s, «expr∞»()))
(hf : «expr∀ᵐ ∂ , »((x), μ.restrict s, «expr ≤ »(«expr∥ ∥»(f x), C))) : has_finite_integral f (μ.restrict s) :=
by haveI [] [":", expr is_finite_measure (μ.restrict s)] [":=", expr ⟨by rwa ["[", expr measure.restrict_apply_univ, "]"] []⟩]; exact [expr has_finite_integral_of_bounded hf]

variable [NormedGroup E] [MeasurableSpace E] {f g : α → E} {s t : Set α} {μ ν : Measureₓ α}

/-- A function is `integrable_on` a set `s` if it is almost everywhere measurable on `s` and if the
integral of its pointwise norm over `s` is less than infinity. -/
def integrable_on (f : α → E) (s : Set α)
  (μ : Measureₓ α :=  by 
    runTac 
      volume_tac) :
  Prop :=
  integrable f (μ.restrict s)

theorem integrable_on.integrable (h : integrable_on f s μ) : integrable f (μ.restrict s) :=
  h

@[simp]
theorem integrable_on_empty : integrable_on f ∅ μ :=
  by 
    simp [integrable_on, integrable_zero_measure]

@[simp]
theorem integrable_on_univ : integrable_on f univ μ ↔ integrable f μ :=
  by 
    rw [integrable_on, measure.restrict_univ]

theorem integrable_on_zero : integrable_on (fun _ => (0 : E)) s μ :=
  integrable_zero _ _ _

@[simp]
theorem integrable_on_const {C : E} : integrable_on (fun _ => C) s μ ↔ C = 0 ∨ μ s < ∞ :=
  integrable_const_iff.trans$
    by 
      rw [measure.restrict_apply_univ]

theorem integrable_on.mono (h : integrable_on f t ν) (hs : s ⊆ t) (hμ : μ ≤ ν) : integrable_on f s μ :=
  h.mono_measure$ measure.restrict_mono hs hμ

theorem integrable_on.mono_set (h : integrable_on f t μ) (hst : s ⊆ t) : integrable_on f s μ :=
  h.mono hst (le_reflₓ _)

theorem integrable_on.mono_measure (h : integrable_on f s ν) (hμ : μ ≤ ν) : integrable_on f s μ :=
  h.mono (subset.refl _) hμ

theorem integrable_on.mono_set_ae (h : integrable_on f t μ) (hst : s ≤ᵐ[μ] t) : integrable_on f s μ :=
  h.integrable.mono_measure$ measure.restrict_mono_ae hst

theorem integrable_on.congr_set_ae (h : integrable_on f t μ) (hst : s =ᵐ[μ] t) : integrable_on f s μ :=
  h.mono_set_ae hst.le

theorem integrable.integrable_on (h : integrable f μ) : integrable_on f s μ :=
  h.mono_measure$ measure.restrict_le_self

theorem integrable.integrable_on' (h : integrable f (μ.restrict s)) : integrable_on f s μ :=
  h

theorem integrable_on.restrict (h : integrable_on f s μ) (hs : MeasurableSet s) : integrable_on f s (μ.restrict t) :=
  by 
    rw [integrable_on, measure.restrict_restrict hs]
    exact h.mono_set (inter_subset_left _ _)

theorem integrable_on.left_of_union (h : integrable_on f (s ∪ t) μ) : integrable_on f s μ :=
  h.mono_set$ subset_union_left _ _

theorem integrable_on.right_of_union (h : integrable_on f (s ∪ t) μ) : integrable_on f t μ :=
  h.mono_set$ subset_union_right _ _

theorem integrable_on.union (hs : integrable_on f s μ) (ht : integrable_on f t μ) : integrable_on f (s ∪ t) μ :=
  (hs.add_measure ht).mono_measure$ measure.restrict_union_le _ _

@[simp]
theorem integrable_on_union : integrable_on f (s ∪ t) μ ↔ integrable_on f s μ ∧ integrable_on f t μ :=
  ⟨fun h => ⟨h.left_of_union, h.right_of_union⟩, fun h => h.1.union h.2⟩

-- error in MeasureTheory.Integral.IntegrableOn: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
@[simp]
theorem integrable_on_singleton_iff
{x : α}
[measurable_singleton_class α] : «expr ↔ »(integrable_on f {x} μ, «expr ∨ »(«expr = »(f x, 0), «expr < »(μ {x}, «expr∞»()))) :=
begin
  have [] [":", expr «expr =ᵐ[ ] »(f, μ.restrict {x}, λ y, f x)] [],
  { filter_upwards ["[", expr ae_restrict_mem (measurable_set_singleton x), "]"] [],
    assume [binders (a ha)],
    simp [] [] ["only"] ["[", expr mem_singleton_iff.1 ha, "]"] [] [] },
  rw ["[", expr integrable_on, ",", expr integrable_congr this, ",", expr integrable_const_iff, "]"] [],
  simp [] [] [] [] [] []
end

@[simp]
theorem integrable_on_finite_Union {s : Set β} (hs : finite s) {t : β → Set α} :
  integrable_on f (⋃(i : _)(_ : i ∈ s), t i) μ ↔ ∀ i _ : i ∈ s, integrable_on f (t i) μ :=
  by 
    apply hs.induction_on
    ·
      simp 
    ·
      intro a s ha hs hf 
      simp [hf, or_imp_distrib, forall_and_distrib]

@[simp]
theorem integrable_on_finset_Union {s : Finset β} {t : β → Set α} :
  integrable_on f (⋃(i : _)(_ : i ∈ s), t i) μ ↔ ∀ i _ : i ∈ s, integrable_on f (t i) μ :=
  integrable_on_finite_Union s.finite_to_set

@[simp]
theorem integrable_on_fintype_Union [Fintype β] {t : β → Set α} :
  integrable_on f (⋃i, t i) μ ↔ ∀ i, integrable_on f (t i) μ :=
  by 
    simpa using @integrable_on_finset_Union _ _ _ _ _ _ f μ Finset.univ t

theorem integrable_on.add_measure (hμ : integrable_on f s μ) (hν : integrable_on f s ν) : integrable_on f s (μ+ν) :=
  by 
    delta' integrable_on 
    rw [measure.restrict_add]
    exact hμ.integrable.add_measure hν

@[simp]
theorem integrable_on_add_measure : integrable_on f s (μ+ν) ↔ integrable_on f s μ ∧ integrable_on f s ν :=
  ⟨fun h => ⟨h.mono_measure (measure.le_add_right (le_reflₓ _)), h.mono_measure (measure.le_add_left (le_reflₓ _))⟩,
    fun h => h.1.add_measure h.2⟩

theorem _root_.measurable_embedding.integrable_on_map_iff [MeasurableSpace β] {e : α → β} (he : MeasurableEmbedding e)
  {f : β → E} {μ : Measureₓ α} {s : Set β} : integrable_on f s (measure.map e μ) ↔ integrable_on (f ∘ e) (e ⁻¹' s) μ :=
  by 
    simp only [integrable_on, he.restrict_map, he.integrable_map_iff]

theorem integrable_on_map_equiv [MeasurableSpace β] (e : α ≃ᵐ β) {f : β → E} {μ : Measureₓ α} {s : Set β} :
  integrable_on f s (measure.map e μ) ↔ integrable_on (f ∘ e) (e ⁻¹' s) μ :=
  by 
    simp only [integrable_on, e.restrict_map, integrable_map_equiv e]

theorem measure_preserving.integrable_on_comp_preimage [MeasurableSpace β] {e : α → β} {ν}
  (h₁ : measure_preserving e μ ν) (h₂ : MeasurableEmbedding e) {f : β → E} {s : Set β} :
  integrable_on (f ∘ e) (e ⁻¹' s) μ ↔ integrable_on f s ν :=
  (h₁.restrict_preimage_emb h₂ s).integrable_comp_emb h₂

theorem measure_preserving.integrable_on_image [MeasurableSpace β] {e : α → β} {ν} (h₁ : measure_preserving e μ ν)
  (h₂ : MeasurableEmbedding e) {f : β → E} {s : Set α} : integrable_on f (e '' s) ν ↔ integrable_on (f ∘ e) s μ :=
  ((h₁.restrict_image_emb h₂ s).integrable_comp_emb h₂).symm

theorem integrable_indicator_iff (hs : MeasurableSet s) : integrable (indicator s f) μ ↔ integrable_on f s μ :=
  by 
    simp [integrable_on, integrable, has_finite_integral, nnnorm_indicator_eq_indicator_nnnorm, Ennreal.coe_indicator,
      lintegral_indicator _ hs, ae_measurable_indicator_iff hs]

theorem integrable_on.indicator (h : integrable_on f s μ) (hs : MeasurableSet s) : integrable (indicator s f) μ :=
  (integrable_indicator_iff hs).2 h

theorem integrable.indicator (h : integrable f μ) (hs : MeasurableSet s) : integrable (indicator s f) μ :=
  h.integrable_on.indicator hs

theorem integrable_indicator_const_Lp {E} [NormedGroup E] [MeasurableSpace E] [BorelSpace E]
  [second_countable_topology E] {p : ℝ≥0∞} {s : Set α} (hs : MeasurableSet s) (hμs : μ s ≠ ∞) (c : E) :
  integrable (indicator_const_Lp p hs hμs c) μ :=
  by 
    rw [integrable_congr indicator_const_Lp_coe_fn, integrable_indicator_iff hs, integrable_on, integrable_const_iff,
      lt_top_iff_ne_top]
    right 
    simpa only [Set.univ_inter, MeasurableSet.univ, measure.restrict_apply] using hμs

-- error in MeasureTheory.Integral.IntegrableOn: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem integrable_on_Lp_of_measure_ne_top
{E}
[normed_group E]
[measurable_space E]
[borel_space E]
[second_countable_topology E]
{p : «exprℝ≥0∞»()}
{s : set α}
(f : Lp E p μ)
(hp : «expr ≤ »(1, p))
(hμs : «expr ≠ »(μ s, «expr∞»())) : integrable_on f s μ :=
begin
  refine [expr mem_ℒp_one_iff_integrable.mp _],
  have [ident hμ_restrict_univ] [":", expr «expr < »(μ.restrict s set.univ, «expr∞»())] [],
  by simpa [] [] ["only"] ["[", expr set.univ_inter, ",", expr measurable_set.univ, ",", expr measure.restrict_apply, ",", expr lt_top_iff_ne_top, "]"] [] [],
  haveI [ident hμ_finite] [":", expr is_finite_measure (μ.restrict s)] [":=", expr ⟨hμ_restrict_univ⟩],
  exact [expr ((Lp.mem_ℒp _).restrict s).mem_ℒp_of_exponent_le hp]
end

/-- We say that a function `f` is *integrable at filter* `l` if it is integrable on some
set `s ∈ l`. Equivalently, it is eventually integrable on `s` in `l.lift' powerset`. -/
def integrable_at_filter (f : α → E) (l : Filter α)
  (μ : Measureₓ α :=  by 
    runTac 
      volume_tac) :=
  ∃ (s : _)(_ : s ∈ l), integrable_on f s μ

variable {l l' : Filter α}

protected theorem integrable_at_filter.eventually (h : integrable_at_filter f l μ) :
  ∀ᶠs in l.lift' powerset, integrable_on f s μ :=
  by 
    refine' (eventually_lift'_powerset'$ fun s t hst ht => _).2 h 
    exact ht.mono_set hst

theorem integrable_at_filter.filter_mono (hl : l ≤ l') (hl' : integrable_at_filter f l' μ) :
  integrable_at_filter f l μ :=
  let ⟨s, hs, hsf⟩ := hl'
  ⟨s, hl hs, hsf⟩

theorem integrable_at_filter.inf_of_left (hl : integrable_at_filter f l μ) : integrable_at_filter f (l⊓l') μ :=
  hl.filter_mono inf_le_left

theorem integrable_at_filter.inf_of_right (hl : integrable_at_filter f l μ) : integrable_at_filter f (l'⊓l) μ :=
  hl.filter_mono inf_le_right

@[simp]
theorem integrable_at_filter.inf_ae_iff {l : Filter α} :
  integrable_at_filter f (l⊓μ.ae) μ ↔ integrable_at_filter f l μ :=
  by 
    refine' ⟨_, fun h => h.filter_mono inf_le_left⟩
    rintro ⟨s, ⟨t, ht, u, hu, rfl⟩, hf⟩
    refine' ⟨t, ht, _⟩
    refine' hf.integrable.mono_measure fun v hv => _ 
    simp only [measure.restrict_apply hv]
    refine' measure_mono_ae (mem_of_superset hu$ fun x hx => _)
    exact fun ⟨hv, ht⟩ => ⟨hv, ⟨ht, hx⟩⟩

alias integrable_at_filter.inf_ae_iff ↔ MeasureTheory.IntegrableAtFilter.of_inf_ae _

/-- If `μ` is a measure finite at filter `l` and `f` is a function such that its norm is bounded
above at `l`, then `f` is integrable at `l`. -/
theorem measure.finite_at_filter.integrable_at_filter {l : Filter α} [is_measurably_generated l]
  (hfm : MeasurableAtFilter f l μ) (hμ : μ.finite_at_filter l) (hf : l.is_bounded_under (· ≤ ·) (norm ∘ f)) :
  integrable_at_filter f l μ :=
  by 
    obtain ⟨C, hC⟩ : ∃ C, ∀ᶠs in l.lift' powerset, ∀ x _ : x ∈ s, ∥f x∥ ≤ C 
    exact hf.imp fun C hC => eventually_lift'_powerset.2 ⟨_, hC, fun t => id⟩
    rcases(hfm.eventually.and (hμ.eventually.and hC)).exists_measurable_mem_of_lift' with ⟨s, hsl, hsm, hfm, hμ, hC⟩
    refine' ⟨s, hsl, ⟨hfm, has_finite_integral_restrict_of_bounded hμ _⟩⟩
    exact C 
    rw [ae_restrict_eq hsm, eventually_inf_principal]
    exact eventually_of_forall hC

theorem measure.finite_at_filter.integrable_at_filter_of_tendsto_ae {l : Filter α} [is_measurably_generated l]
  (hfm : MeasurableAtFilter f l μ) (hμ : μ.finite_at_filter l) {b} (hf : tendsto f (l⊓μ.ae) (𝓝 b)) :
  integrable_at_filter f l μ :=
  (hμ.inf_of_left.integrable_at_filter (hfm.filter_mono inf_le_left) hf.norm.is_bounded_under_le).of_inf_ae

alias measure.finite_at_filter.integrable_at_filter_of_tendsto_ae ← Filter.Tendsto.integrable_at_filter_ae

theorem measure.finite_at_filter.integrable_at_filter_of_tendsto {l : Filter α} [is_measurably_generated l]
  (hfm : MeasurableAtFilter f l μ) (hμ : μ.finite_at_filter l) {b} (hf : tendsto f l (𝓝 b)) :
  integrable_at_filter f l μ :=
  hμ.integrable_at_filter hfm hf.norm.is_bounded_under_le

alias measure.finite_at_filter.integrable_at_filter_of_tendsto ← Filter.Tendsto.integrable_at_filter

variable [BorelSpace E] [second_countable_topology E]

theorem integrable_add_of_disjoint {f g : α → E} (h : Disjoint (support f) (support g)) (hf : Measurable f)
  (hg : Measurable g) : integrable (f+g) μ ↔ integrable f μ ∧ integrable g μ :=
  by 
    refine' ⟨fun hfg => ⟨_, _⟩, fun h => h.1.add h.2⟩
    ·
      rw [←indicator_add_eq_left h]
      exact hfg.indicator (measurable_set_support hf)
    ·
      rw [←indicator_add_eq_right h]
      exact hfg.indicator (measurable_set_support hg)

end NormedGroup

end MeasureTheory

open MeasureTheory

variable [MeasurableSpace E] [NormedGroup E]

/-- If a function is integrable at `𝓝[s] x` for each point `x` of a compact set `s`, then it is
integrable on `s`. -/
theorem IsCompact.integrable_on_of_nhds_within [TopologicalSpace α] {μ : Measureₓ α} {s : Set α} (hs : IsCompact s)
  {f : α → E} (hf : ∀ x _ : x ∈ s, integrable_at_filter f (𝓝[s] x) μ) : integrable_on f s μ :=
  IsCompact.induction_on hs integrable_on_empty (fun s t hst ht => ht.mono_set hst) (fun s t hs ht => hs.union ht) hf

-- error in MeasureTheory.Integral.IntegrableOn: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- A function which is continuous on a set `s` is almost everywhere measurable with respect to
`μ.restrict s`. -/
theorem continuous_on.ae_measurable
[topological_space α]
[opens_measurable_space α]
[measurable_space β]
[topological_space β]
[borel_space β]
{f : α → β}
{s : set α}
{μ : measure α}
(hf : continuous_on f s)
(hs : measurable_set s) : ae_measurable f (μ.restrict s) :=
begin
  nontriviality [expr α] [],
  inhabit [expr α] [],
  have [] [":", expr «expr =ᵐ[ ] »(piecewise s f (λ
     _, f (default α)), μ.restrict s, f)] [":=", expr piecewise_ae_eq_restrict hs],
  refine [expr ⟨piecewise s f (λ _, f (default α)), _, this.symm⟩],
  apply [expr measurable_of_is_open],
  assume [binders (t ht)],
  obtain ["⟨", ident u, ",", ident u_open, ",", ident hu, "⟩", ":", expr «expr∃ , »((u : set α), «expr ∧ »(is_open u, «expr = »(«expr ∩ »(«expr ⁻¹' »(f, t), s), «expr ∩ »(u, s)))), ":=", expr _root_.continuous_on_iff'.1 hf t ht],
  rw ["[", expr piecewise_preimage, ",", expr set.ite, ",", expr hu, "]"] [],
  exact [expr (u_open.measurable_set.inter hs).union ((measurable_const ht.measurable_set).diff hs)]
end

-- error in MeasureTheory.Integral.IntegrableOn: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem continuous_on.integrable_at_nhds_within
[topological_space α]
[opens_measurable_space α]
[borel_space E]
{μ : measure α}
[is_locally_finite_measure μ]
{a : α}
{t : set α}
{f : α → E}
(hft : continuous_on f t)
(ht : measurable_set t)
(ha : «expr ∈ »(a, t)) : integrable_at_filter f «expr𝓝[ ] »(t, a) μ :=
by haveI [] [":", expr «expr𝓝[ ] »(t, a).is_measurably_generated] [":=", expr ht.nhds_within_is_measurably_generated _]; exact [expr (hft a ha).integrable_at_filter ⟨_, self_mem_nhds_within, hft.ae_measurable ht⟩ (μ.finite_at_nhds_within _ _)]

/-- A function `f` continuous on a compact set `s` is integrable on this set with respect to any
locally finite measure. -/
theorem ContinuousOn.integrable_on_compact [TopologicalSpace α] [OpensMeasurableSpace α] [BorelSpace E] [T2Space α]
  {μ : Measureₓ α} [is_locally_finite_measure μ] {s : Set α} (hs : IsCompact s) {f : α → E} (hf : ContinuousOn f s) :
  integrable_on f s μ :=
  hs.integrable_on_of_nhds_within$ fun x hx => hf.integrable_at_nhds_within hs.measurable_set hx

theorem ContinuousOn.integrable_on_Icc [BorelSpace E] [ConditionallyCompleteLinearOrder β] [TopologicalSpace β]
  [OrderTopology β] [MeasurableSpace β] [OpensMeasurableSpace β] {μ : Measureₓ β} [is_locally_finite_measure μ]
  {a b : β} {f : β → E} (hf : ContinuousOn f (Icc a b)) : integrable_on f (Icc a b) μ :=
  hf.integrable_on_compact is_compact_Icc

-- error in MeasureTheory.Integral.IntegrableOn: ././Mathport/Syntax/Translate/Basic.lean:546:47: unsupported (impossible)
theorem continuous_on.integrable_on_interval
[borel_space E]
[conditionally_complete_linear_order β]
[topological_space β]
[order_topology β]
[measurable_space β]
[opens_measurable_space β]
{μ : measure β}
[is_locally_finite_measure μ]
{a b : β}
{f : β → E}
(hf : continuous_on f «expr[ , ]»(a, b)) : integrable_on f «expr[ , ]»(a, b) μ :=
hf.integrable_on_compact is_compact_interval

/-- A continuous function `f` is integrable on any compact set with respect to any locally finite
measure. -/
theorem Continuous.integrable_on_compact [TopologicalSpace α] [OpensMeasurableSpace α] [T2Space α] [BorelSpace E]
  {μ : Measureₓ α} [is_locally_finite_measure μ] {s : Set α} (hs : IsCompact s) {f : α → E} (hf : Continuous f) :
  integrable_on f s μ :=
  hf.continuous_on.integrable_on_compact hs

theorem Continuous.integrable_on_Icc [BorelSpace E] [ConditionallyCompleteLinearOrder β] [TopologicalSpace β]
  [OrderTopology β] [MeasurableSpace β] [OpensMeasurableSpace β] {μ : Measureₓ β} [is_locally_finite_measure μ]
  {a b : β} {f : β → E} (hf : Continuous f) : integrable_on f (Icc a b) μ :=
  hf.integrable_on_compact is_compact_Icc

theorem Continuous.integrable_on_Ioc [BorelSpace E] [ConditionallyCompleteLinearOrder β] [TopologicalSpace β]
  [OrderTopology β] [MeasurableSpace β] [OpensMeasurableSpace β] {μ : Measureₓ β} [is_locally_finite_measure μ]
  {a b : β} {f : β → E} (hf : Continuous f) : integrable_on f (Ioc a b) μ :=
  hf.integrable_on_Icc.mono_set Ioc_subset_Icc_self

-- error in MeasureTheory.Integral.IntegrableOn: ././Mathport/Syntax/Translate/Basic.lean:546:47: unsupported (impossible)
theorem continuous.integrable_on_interval
[borel_space E]
[conditionally_complete_linear_order β]
[topological_space β]
[order_topology β]
[measurable_space β]
[opens_measurable_space β]
{μ : measure β}
[is_locally_finite_measure μ]
{a b : β}
{f : β → E}
(hf : continuous f) : integrable_on f «expr[ , ]»(a, b) μ :=
hf.integrable_on_compact is_compact_interval

theorem Continuous.integrable_on_interval_oc [BorelSpace E] [ConditionallyCompleteLinearOrder β] [TopologicalSpace β]
  [OrderTopology β] [MeasurableSpace β] [OpensMeasurableSpace β] {μ : Measureₓ β} [is_locally_finite_measure μ]
  {a b : β} {f : β → E} (hf : Continuous f) : integrable_on f (Ι a b) μ :=
  hf.integrable_on_Ioc

/-- A continuous function with compact closure of the support is integrable on the whole space. -/
theorem Continuous.integrable_of_compact_closure_support [TopologicalSpace α] [OpensMeasurableSpace α] [T2Space α]
  [BorelSpace E] {μ : Measureₓ α} [is_locally_finite_measure μ] {f : α → E} (hf : Continuous f)
  (hfc : IsCompact (Closure$ support f)) : integrable f μ :=
  by 
    rw [←indicator_eq_self.2 (@subset_closure _ _ (support f)),
      integrable_indicator_iff is_closed_closure.measurable_set]
    ·
      exact hf.integrable_on_compact hfc
    ·
      infer_instance

section 

variable [TopologicalSpace α] [OpensMeasurableSpace α] {μ : Measureₓ α} {s t : Set α} {f g : α → ℝ}

-- error in MeasureTheory.Integral.IntegrableOn: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem measure_theory.integrable_on.mul_continuous_on_of_subset
(hf : integrable_on f s μ)
(hg : continuous_on g t)
(hs : measurable_set s)
(ht : is_compact t)
(hst : «expr ⊆ »(s, t)) : integrable_on (λ x, «expr * »(f x, g x)) s μ :=
begin
  rcases [expr is_compact.exists_bound_of_continuous_on ht hg, "with", "⟨", ident C, ",", ident hC, "⟩"],
  rw ["[", expr integrable_on, ",", "<-", expr mem_ℒp_one_iff_integrable, "]"] ["at", ident hf, "⊢"],
  have [] [":", expr «expr∀ᵐ ∂ , »((x), μ.restrict s, «expr ≤ »(«expr∥ ∥»(«expr * »(f x, g x)), «expr * »(C, «expr∥ ∥»(f x))))] [],
  { filter_upwards ["[", expr ae_restrict_mem hs, "]"] [],
    assume [binders (x hx)],
    rw ["[", expr real.norm_eq_abs, ",", expr abs_mul, ",", expr mul_comm, ",", expr real.norm_eq_abs, "]"] [],
    apply [expr mul_le_mul_of_nonneg_right (hC x (hst hx)) (abs_nonneg _)] },
  exact [expr mem_ℒp.of_le_mul hf (hf.ae_measurable.mul ((hg.mono hst).ae_measurable hs)) this]
end

theorem MeasureTheory.IntegrableOn.mul_continuous_on [T2Space α] (hf : integrable_on f s μ) (hg : ContinuousOn g s)
  (hs : IsCompact s) : integrable_on (fun x => f x*g x) s μ :=
  hf.mul_continuous_on_of_subset hg hs.measurable_set hs (subset.refl _)

theorem MeasureTheory.IntegrableOn.continuous_on_mul_of_subset (hf : integrable_on f s μ) (hg : ContinuousOn g t)
  (hs : MeasurableSet s) (ht : IsCompact t) (hst : s ⊆ t) : integrable_on (fun x => g x*f x) s μ :=
  by 
    simpa [mul_commₓ] using hf.mul_continuous_on_of_subset hg hs ht hst

theorem MeasureTheory.IntegrableOn.continuous_on_mul [T2Space α] (hf : integrable_on f s μ) (hg : ContinuousOn g s)
  (hs : IsCompact s) : integrable_on (fun x => g x*f x) s μ :=
  hf.continuous_on_mul_of_subset hg hs.measurable_set hs (subset.refl _)

end 

section Monotone

variable [TopologicalSpace α] [BorelSpace α] [BorelSpace E] [ConditionallyCompleteLinearOrder α]
  [ConditionallyCompleteLinearOrder E] [OrderTopology α] [OrderTopology E] [second_countable_topology E]
  {μ : Measureₓ α} [is_locally_finite_measure μ] {s : Set α} (hs : IsCompact s) {f : α → E}

include hs

-- error in MeasureTheory.Integral.IntegrableOn: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem monotone_on.integrable_on_compact (hmono : monotone_on f s) : integrable_on f s μ :=
begin
  obtain [ident rfl, "|", ident h, ":=", expr s.eq_empty_or_nonempty],
  { exact [expr integrable_on_empty] },
  have [ident hbelow] [":", expr bdd_below «expr '' »(f, s)] [":=", expr ⟨f (Inf s), λ
    (x)
    ⟨y, hy, hyx⟩, «expr ▸ »(hyx, hmono (hs.Inf_mem h) hy (cInf_le hs.bdd_below hy))⟩],
  have [ident habove] [":", expr bdd_above «expr '' »(f, s)] [":=", expr ⟨f (Sup s), λ
    (x)
    ⟨y, hy, hyx⟩, «expr ▸ »(hyx, hmono hy (hs.Sup_mem h) (le_cSup hs.bdd_above hy))⟩],
  have [] [":", expr metric.bounded «expr '' »(f, s)] [":=", expr metric.bounded_of_bdd_above_of_bdd_below habove hbelow],
  rcases [expr bounded_iff_forall_norm_le.mp this, "with", "⟨", ident C, ",", ident hC, "⟩"],
  exact [expr integrable.mono' (continuous_const.integrable_on_compact hs) (ae_measurable_restrict_of_monotone_on hs.measurable_set hmono) «expr $ »((ae_restrict_iff' hs.measurable_set).mpr, «expr $ »(ae_of_all _, λ
     y hy, hC (f y) (mem_image_of_mem f hy)))]
end

theorem AntitoneOn.integrable_on_compact (hanti : AntitoneOn f s) : integrable_on f s μ :=
  @MonotoneOn.integrable_on_compact α (OrderDual E) _ _ ‹_› _ _ ‹_› _ _ _ _ ‹_› _ _ _ hs _ hanti

theorem Monotone.integrable_on_compact (hmono : Monotone f) : integrable_on f s μ :=
  MonotoneOn.integrable_on_compact hs fun x y _ _ hxy => hmono hxy

theorem Antitone.integrable_on_compact (hanti : Antitone f) : integrable_on f s μ :=
  @Monotone.integrable_on_compact α (OrderDual E) _ _ ‹_› _ _ ‹_› _ _ _ _ ‹_› _ _ _ hs _ hanti

end Monotone

