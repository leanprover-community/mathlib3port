import Mathbin.MeasureTheory.Function.SimpleFuncDense

/-!
# Strongly measurable and finitely strongly measurable functions

A function `f` is said to be strongly measurable if `f` is the sequential limit of simple functions.
It is said to be finitely strongly measurable with respect to a measure `μ` if the supports
of those simple functions have finite measure.

If the target space has a second countable topology, strongly measurable and measurable are
equivalent.

Functions in `Lp` for `0 < p < ∞` are finitely strongly measurable.
If the measure is sigma-finite, strongly measurable and finitely strongly measurable are equivalent.

The main property of finitely strongly measurable functions is
`fin_strongly_measurable.exists_set_sigma_finite`: there exists a measurable set `t` such that the
function is supported on `t` and `μ.restrict t` is sigma-finite. As a consequence, we can prove some
results for those functions as if the measure was sigma-finite.

## Main definitions

* `strongly_measurable f`: `f : α → β` is the limit of a sequence `fs : ℕ → simple_func α β`.
* `fin_strongly_measurable f μ`: `f : α → β` is the limit of a sequence `fs : ℕ → simple_func α β`
  such that for all `n ∈ ℕ`, the measure of the support of `fs n` is finite.
* `ae_fin_strongly_measurable f μ`: `f` is almost everywhere equal to a `fin_strongly_measurable`
  function.

* `ae_fin_strongly_measurable.sigma_finite_set`: a measurable set `t` such that
  `f =ᵐ[μ.restrict tᶜ] 0` and `μ.restrict t` is sigma-finite.

## Main statements

* `ae_fin_strongly_measurable.exists_set_sigma_finite`: there exists a measurable set `t` such that
  `f =ᵐ[μ.restrict tᶜ] 0` and `μ.restrict t` is sigma-finite.
* `mem_ℒp.ae_fin_strongly_measurable`: if `mem_ℒp f p μ` with `0 < p < ∞`, then
  `ae_fin_strongly_measurable f μ`.
* `Lp.fin_strongly_measurable`: for `0 < p < ∞`, `Lp` functions are finitely strongly measurable.

## References

* Hytönen, Tuomas, Jan Van Neerven, Mark Veraar, and Lutz Weis. Analysis in Banach spaces.
  Springer, 2016.

-/


open MeasureTheory Filter TopologicalSpace Function

open_locale Ennreal TopologicalSpace MeasureTheory

namespace MeasureTheory

local infixr:25 " →ₛ " => simple_func

section Definitions

variable {α β : Type _} [TopologicalSpace β]

/-- A function is `strongly_measurable` if it is the limit of simple functions. -/
def strongly_measurable [MeasurableSpace α] (f : α → β) : Prop :=
  ∃ fs : ℕ → α →ₛ β, ∀ x, tendsto (fun n => fs n x) at_top (𝓝 (f x))

/-- A function is `fin_strongly_measurable` with respect to a measure if it is the limit of simple
  functions with support with finite measure. -/
def fin_strongly_measurable [Zero β] {m0 : MeasurableSpace α} (f : α → β) (μ : Measureₓ α) : Prop :=
  ∃ fs : ℕ → α →ₛ β, (∀ n, μ (support (fs n)) < ∞) ∧ ∀ x, tendsto (fun n => fs n x) at_top (𝓝 (f x))

/-- A function is `ae_fin_strongly_measurable` with respect to a measure if it is almost everywhere
equal to the limit of a sequence of simple functions with support with finite measure. -/
def ae_fin_strongly_measurable [Zero β] {m0 : MeasurableSpace α} (f : α → β) (μ : Measureₓ α) : Prop :=
  ∃ g, fin_strongly_measurable g μ ∧ f =ᵐ[μ] g

end Definitions

/-! ## Strongly measurable functions -/


theorem subsingleton.strongly_measurable {α β} [MeasurableSpace α] [TopologicalSpace β] [Subsingleton β] (f : α → β) :
    strongly_measurable f := by
  let f_sf : α →ₛ β := ⟨f, fun x => _, Set.Subsingleton.finite Set.subsingleton_of_subsingleton⟩
  · exact ⟨fun n => f_sf, fun x => tendsto_const_nhds⟩
    
  · have h_univ : f ⁻¹' {x} = Set.Univ := by
      ext1 y
      simp
    rw [h_univ]
    exact MeasurableSet.univ
    

namespace StronglyMeasurable

variable {α β : Type _} {f g : α → β}

/-- A sequence of simple functions such that `∀ x, tendsto (λ n, hf.approx n x) at_top (𝓝 (f x))`.
That property is given by `strongly_measurable.tendsto_approx`. -/
protected noncomputable def approx [MeasurableSpace α] [TopologicalSpace β] (hf : strongly_measurable f) : ℕ → α →ₛ β :=
  hf.some

protected theorem tendsto_approx [MeasurableSpace α] [TopologicalSpace β] (hf : strongly_measurable f) :
    ∀ x, tendsto (fun n => hf.approx n x) at_top (𝓝 (f x)) :=
  hf.some_spec

-- ././Mathport/Syntax/Translate/Basic.lean:480:2: warning: expanding binder collection (x «expr ∉ » t)
theorem fin_strongly_measurable_of_set_sigma_finite [TopologicalSpace β] [Zero β] {m : MeasurableSpace α}
    {μ : Measureₓ α} (hf_meas : strongly_measurable f) {t : Set α} (ht : MeasurableSet t)
    (hft_zero : ∀, ∀ x ∈ tᶜ, ∀, f x = 0) (htμ : sigma_finite (μ.restrict t)) : fin_strongly_measurable f μ := by
  have : sigma_finite (μ.restrict t) := htμ
  let S := spanning_sets (μ.restrict t)
  have hS_meas : ∀ n, MeasurableSet (S n) := measurable_spanning_sets (μ.restrict t)
  let f_approx := hf_meas.approx
  let fs := fun n => simple_func.restrict (f_approx n) (S n ∩ t)
  have h_fs_t_compl : ∀ n, ∀ x _ : x ∉ t, fs n x = 0 := by
    intro n x hxt
    rw [simple_func.restrict_apply _ ((hS_meas n).inter ht)]
    refine' Set.indicator_of_not_mem _ _
    simp [hxt]
  refine' ⟨fs, _, fun x => _⟩
  · simp_rw [simple_func.support_eq]
    refine' fun n => (measure_bUnion_finset_le _ _).trans_lt _
    refine' ennreal.sum_lt_top_iff.mpr fun y hy => _
    rw [simple_func.restrict_preimage_singleton _ ((hS_meas n).inter ht)]
    swap
    · rw [Finset.mem_filter] at hy
      exact hy.2
      
    refine' (measure_mono (Set.inter_subset_left _ _)).trans_lt _
    have h_lt_top := measure_spanning_sets_lt_top (μ.restrict t) n
    rwa [measure.restrict_apply' ht] at h_lt_top
    
  · by_cases' hxt : x ∈ t
    swap
    · rw [funext fun n => h_fs_t_compl n x hxt, hft_zero x hxt]
      exact tendsto_const_nhds
      
    have h : tendsto (fun n => (f_approx n) x) at_top (𝓝 (f x)) := hf_meas.tendsto_approx x
    obtain ⟨n₁, hn₁⟩ : ∃ n, ∀ m, n ≤ m → fs m x = f_approx m x := by
      obtain ⟨n, hn⟩ : ∃ n, ∀ m, n ≤ m → x ∈ S m ∩ t := by
        suffices ∃ n, ∀ m, n ≤ m → x ∈ S m by
          obtain ⟨n, hn⟩ := this
          exact ⟨n, fun m hnm => Set.mem_inter (hn m hnm) hxt⟩
        suffices ∃ n, x ∈ S n by
          rcases this with ⟨n, hn⟩
          exact ⟨n, fun m hnm => monotone_spanning_sets (μ.restrict t) hnm hn⟩
        rw [← Set.mem_Union, Union_spanning_sets (μ.restrict t)]
        trivial
      refine' ⟨n, fun m hnm => _⟩
      simp_rw [fs, simple_func.restrict_apply _ ((hS_meas m).inter ht), Set.indicator_of_mem (hn m hnm)]
    rw [tendsto_at_top'] at h⊢
    intro s hs
    obtain ⟨n₂, hn₂⟩ := h s hs
    refine' ⟨max n₁ n₂, fun m hm => _⟩
    rw [hn₁ m ((le_max_leftₓ _ _).trans hm.le)]
    exact hn₂ m ((le_max_rightₓ _ _).trans hm.le)
    

/-- If the measure is sigma-finite, all strongly measurable functions are
  `fin_strongly_measurable`. -/
protected theorem fin_strongly_measurable [TopologicalSpace β] [Zero β] {m0 : MeasurableSpace α}
    (hf : strongly_measurable f) (μ : Measureₓ α) [sigma_finite μ] : fin_strongly_measurable f μ :=
  hf.fin_strongly_measurable_of_set_sigma_finite MeasurableSet.univ
    (by
      simp )
    (by
      rwa [measure.restrict_univ])

/-- A strongly measurable function is measurable. -/
protected theorem Measurable [MeasurableSpace α] [MetricSpace β] [MeasurableSpace β] [BorelSpace β]
    (hf : strongly_measurable f) : Measurable f :=
  measurable_of_tendsto_metric (fun n => (hf.approx n).Measurable) (tendsto_pi_nhds.mpr hf.tendsto_approx)

section Arithmetic

variable [MeasurableSpace α] [TopologicalSpace β]

protected theorem add [Add β] [HasContinuousAdd β] (hf : strongly_measurable f) (hg : strongly_measurable g) :
    strongly_measurable (f + g) :=
  ⟨fun n => hf.approx n + hg.approx n, fun x => (hf.tendsto_approx x).add (hg.tendsto_approx x)⟩

protected theorem neg [AddGroupₓ β] [TopologicalAddGroup β] (hf : strongly_measurable f) : strongly_measurable (-f) :=
  ⟨fun n => -hf.approx n, fun x => (hf.tendsto_approx x).neg⟩

protected theorem sub [Sub β] [HasContinuousSub β] (hf : strongly_measurable f) (hg : strongly_measurable g) :
    strongly_measurable (f - g) :=
  ⟨fun n => hf.approx n - hg.approx n, fun x => (hf.tendsto_approx x).sub (hg.tendsto_approx x)⟩

end Arithmetic

end StronglyMeasurable

section SecondCountableStronglyMeasurable

variable {α β : Type _} [MeasurableSpace α] [MeasurableSpace β] {f : α → β}

/-- In a space with second countable topology, measurable implies strongly measurable. -/
theorem _root_.measurable.strongly_measurable [EmetricSpace β] [OpensMeasurableSpace β] [second_countable_topology β]
    (hf : Measurable f) : strongly_measurable f := by
  rcases is_empty_or_nonempty β with ⟨⟩ <;> skip
  · exact subsingleton.strongly_measurable f
    
  · inhabit β
    exact
      ⟨simple_func.approx_on f hf Set.Univ default (Set.mem_univ _), fun x =>
        simple_func.tendsto_approx_on hf (Set.mem_univ _)
          (by
            simp )⟩
    

/-- In a space with second countable topology, strongly measurable and measurable are equivalent. -/
theorem strongly_measurable_iff_measurable [MetricSpace β] [BorelSpace β] [second_countable_topology β] :
    strongly_measurable f ↔ Measurable f :=
  ⟨fun h => h.measurable, fun h => Measurable.strongly_measurable h⟩

end SecondCountableStronglyMeasurable

/-! ## Finitely strongly measurable functions -/


namespace FinStronglyMeasurable

variable {α β : Type _} [Zero β] {m0 : MeasurableSpace α} {μ : Measureₓ α} {f : α → β}

theorem ae_fin_strongly_measurable [TopologicalSpace β] (hf : fin_strongly_measurable f μ) :
    ae_fin_strongly_measurable f μ :=
  ⟨f, hf, ae_eq_refl f⟩

section sequence

variable [TopologicalSpace β] (hf : fin_strongly_measurable f μ)

/-- A sequence of simple functions such that `∀ x, tendsto (λ n, hf.approx n x) at_top (𝓝 (f x))`
and `∀ n, μ (support (hf.approx n)) < ∞`. These properties are given by
`fin_strongly_measurable.tendsto_approx` and `fin_strongly_measurable.fin_support_approx`. -/
protected noncomputable def approx : ℕ → α →ₛ β :=
  hf.some

protected theorem fin_support_approx : ∀ n, μ (support (hf.approx n)) < ∞ :=
  hf.some_spec.1

protected theorem tendsto_approx : ∀ x, tendsto (fun n => hf.approx n x) at_top (𝓝 (f x)) :=
  hf.some_spec.2

end sequence

protected theorem strongly_measurable [TopologicalSpace β] (hf : fin_strongly_measurable f μ) : strongly_measurable f :=
  ⟨hf.approx, hf.tendsto_approx⟩

theorem exists_set_sigma_finite [TopologicalSpace β] [T2Space β] (hf : fin_strongly_measurable f μ) :
    ∃ t, MeasurableSet t ∧ (∀, ∀ x ∈ tᶜ, ∀, f x = 0) ∧ sigma_finite (μ.restrict t) := by
  rcases hf with ⟨fs, hT_lt_top, h_approx⟩
  let T := fun n => support (fs n)
  have hT_meas : ∀ n, MeasurableSet (T n) := fun n => simple_func.measurable_set_support (fs n)
  let t := ⋃ n, T n
  refine' ⟨t, MeasurableSet.Union hT_meas, _, _⟩
  · have h_fs_zero : ∀ n, ∀, ∀ x ∈ tᶜ, ∀, fs n x = 0 := by
      intro n x hxt
      rw [Set.mem_compl_iff, Set.mem_Union, not_exists] at hxt
      simpa using hxt n
    refine' fun x hxt => tendsto_nhds_unique (h_approx x) _
    rw [funext fun n => h_fs_zero n x hxt]
    exact tendsto_const_nhds
    
  · refine' ⟨⟨⟨fun n => tᶜ ∪ T n, fun n => trivialₓ, fun n => _, _⟩⟩⟩
    · rw [measure.restrict_apply' (MeasurableSet.Union hT_meas), Set.union_inter_distrib_right, Set.compl_inter_self t,
        Set.empty_union]
      exact (measure_mono (Set.inter_subset_left _ _)).trans_lt (hT_lt_top n)
      
    · rw [← Set.union_Union (tᶜ) T]
      exact Set.compl_union_self _
      
    

/-- A finitely strongly measurable function is measurable. -/
protected theorem Measurable [MetricSpace β] [MeasurableSpace β] [BorelSpace β] (hf : fin_strongly_measurable f μ) :
    Measurable f :=
  measurable_of_tendsto_metric (fun n => (hf.some n).Measurable) (tendsto_pi_nhds.mpr hf.some_spec.2)

protected theorem add {β} [TopologicalSpace β] [AddMonoidₓ β] [HasContinuousAdd β] {f g : α → β}
    (hf : fin_strongly_measurable f μ) (hg : fin_strongly_measurable g μ) : fin_strongly_measurable (f + g) μ :=
  ⟨fun n => hf.approx n + hg.approx n, fun n =>
    (measure_mono (Function.support_add _ _)).trans_lt
      ((measure_union_le _ _).trans_lt (Ennreal.add_lt_top.mpr ⟨hf.fin_support_approx n, hg.fin_support_approx n⟩)),
    fun x => (hf.tendsto_approx x).add (hg.tendsto_approx x)⟩

protected theorem neg {β} [TopologicalSpace β] [AddGroupₓ β] [TopologicalAddGroup β] {f : α → β}
    (hf : fin_strongly_measurable f μ) : fin_strongly_measurable (-f) μ := by
  refine' ⟨fun n => -hf.approx n, fun n => _, fun x => (hf.tendsto_approx x).neg⟩
  suffices μ (Function.Support fun x => -(hf.approx n) x) < ∞ by
    convert this
  rw [Function.support_neg (hf.approx n)]
  exact hf.fin_support_approx n

protected theorem sub {β} [TopologicalSpace β] [AddGroupₓ β] [HasContinuousSub β] {f g : α → β}
    (hf : fin_strongly_measurable f μ) (hg : fin_strongly_measurable g μ) : fin_strongly_measurable (f - g) μ :=
  ⟨fun n => hf.approx n - hg.approx n, fun n =>
    (measure_mono (Function.support_sub _ _)).trans_lt
      ((measure_union_le _ _).trans_lt (Ennreal.add_lt_top.mpr ⟨hf.fin_support_approx n, hg.fin_support_approx n⟩)),
    fun x => (hf.tendsto_approx x).sub (hg.tendsto_approx x)⟩

end FinStronglyMeasurable

theorem fin_strongly_measurable_iff_strongly_measurable_and_exists_set_sigma_finite {α β} {f : α → β}
    [TopologicalSpace β] [T2Space β] [Zero β] {m : MeasurableSpace α} {μ : Measureₓ α} :
    fin_strongly_measurable f μ ↔
      strongly_measurable f ∧ ∃ t, MeasurableSet t ∧ (∀, ∀ x ∈ tᶜ, ∀, f x = 0) ∧ sigma_finite (μ.restrict t) :=
  ⟨fun hf => ⟨hf.strongly_measurable, hf.exists_set_sigma_finite⟩, fun hf =>
    hf.1.fin_strongly_measurable_of_set_sigma_finite hf.2.some_spec.1 hf.2.some_spec.2.1 hf.2.some_spec.2.2⟩

namespace AeFinStronglyMeasurable

variable {α β : Type _} {m : MeasurableSpace α} {μ : Measureₓ α} [TopologicalSpace β] {f g : α → β}

protected theorem add [AddMonoidₓ β] [HasContinuousAdd β] (hf : ae_fin_strongly_measurable f μ)
    (hg : ae_fin_strongly_measurable g μ) : ae_fin_strongly_measurable (f + g) μ :=
  ⟨hf.some + hg.some, hf.some_spec.1.add hg.some_spec.1, hf.some_spec.2.add hg.some_spec.2⟩

protected theorem neg [AddGroupₓ β] [TopologicalAddGroup β] (hf : ae_fin_strongly_measurable f μ) :
    ae_fin_strongly_measurable (-f) μ :=
  ⟨-hf.some, hf.some_spec.1.neg, hf.some_spec.2.neg⟩

protected theorem sub [AddGroupₓ β] [HasContinuousSub β] (hf : ae_fin_strongly_measurable f μ)
    (hg : ae_fin_strongly_measurable g μ) : ae_fin_strongly_measurable (f - g) μ :=
  ⟨hf.some - hg.some, hf.some_spec.1.sub hg.some_spec.1, hf.some_spec.2.sub hg.some_spec.2⟩

variable [Zero β] [T2Space β]

theorem exists_set_sigma_finite (hf : ae_fin_strongly_measurable f μ) :
    ∃ t, MeasurableSet t ∧ f =ᵐ[μ.restrict (tᶜ)] 0 ∧ sigma_finite (μ.restrict t) := by
  rcases hf with ⟨g, hg, hfg⟩
  obtain ⟨t, ht, hgt_zero, htμ⟩ := hg.exists_set_sigma_finite
  refine' ⟨t, ht, _, htμ⟩
  refine' eventually_eq.trans (ae_restrict_of_ae hfg) _
  rw [eventually_eq, ae_restrict_iff' ht.compl]
  exact eventually_of_forall hgt_zero

/-- A measurable set `t` such that `f =ᵐ[μ.restrict tᶜ] 0` and `sigma_finite (μ.restrict t)`. -/
def sigma_finite_set (hf : ae_fin_strongly_measurable f μ) : Set α :=
  hf.exists_set_sigma_finite.some

protected theorem MeasurableSet (hf : ae_fin_strongly_measurable f μ) : MeasurableSet hf.sigma_finite_set :=
  hf.exists_set_sigma_finite.some_spec.1

theorem ae_eq_zero_compl (hf : ae_fin_strongly_measurable f μ) : f =ᵐ[μ.restrict (hf.sigma_finite_setᶜ)] 0 :=
  hf.exists_set_sigma_finite.some_spec.2.1

instance sigma_finite_restrict (hf : ae_fin_strongly_measurable f μ) : sigma_finite (μ.restrict hf.sigma_finite_set) :=
  hf.exists_set_sigma_finite.some_spec.2.2

end AeFinStronglyMeasurable

variable {α G : Type _} {p : ℝ≥0∞} {m m0 : MeasurableSpace α} {μ : Measureₓ α} [NormedGroup G] [MeasurableSpace G]
  [BorelSpace G] [second_countable_topology G] {f : α → G}

/-- In a space with second countable topology and a sigma-finite measure, `fin_strongly_measurable`
  and `measurable` are equivalent. -/
theorem fin_strongly_measurable_iff_measurable {m0 : MeasurableSpace α} (μ : Measureₓ α) [sigma_finite μ] :
    fin_strongly_measurable f μ ↔ Measurable f :=
  ⟨fun h => h.measurable, fun h => (Measurable.strongly_measurable h).FinStronglyMeasurable μ⟩

/-- In a space with second countable topology and a sigma-finite measure,
  `ae_fin_strongly_measurable` and `ae_measurable` are equivalent. -/
theorem ae_fin_strongly_measurable_iff_ae_measurable {m0 : MeasurableSpace α} (μ : Measureₓ α) [sigma_finite μ] :
    ae_fin_strongly_measurable f μ ↔ AeMeasurable f μ := by
  simp_rw [ae_fin_strongly_measurable, AeMeasurable, fin_strongly_measurable_iff_measurable]

theorem mem_ℒp.fin_strongly_measurable_of_measurable (hf : mem_ℒp f p μ) (hf_meas : Measurable f) (hp_ne_zero : p ≠ 0)
    (hp_ne_top : p ≠ ∞) : fin_strongly_measurable f μ := by
  let fs := simple_func.approx_on f hf_meas Set.Univ 0 (Set.mem_univ _)
  refine' ⟨fs, _, _⟩
  · have h_fs_Lp : ∀ n, mem_ℒp (fs n) p μ := simple_func.mem_ℒp_approx_on_univ hf_meas hf
    exact fun n => (fs n).measure_support_lt_top_of_mem_ℒp (h_fs_Lp n) hp_ne_zero hp_ne_top
    
  · exact fun x =>
      simple_func.tendsto_approx_on hf_meas (Set.mem_univ 0)
        (by
          simp )
    

theorem mem_ℒp.ae_fin_strongly_measurable (hf : mem_ℒp f p μ) (hp_ne_zero : p ≠ 0) (hp_ne_top : p ≠ ∞) :
    ae_fin_strongly_measurable f μ :=
  ⟨hf.ae_measurable.mk f,
    ((mem_ℒp_congr_ae hf.ae_measurable.ae_eq_mk).mp hf).fin_strongly_measurable_of_measurable
      hf.ae_measurable.measurable_mk hp_ne_zero hp_ne_top,
    hf.ae_measurable.ae_eq_mk⟩

theorem integrable.ae_fin_strongly_measurable (hf : integrable f μ) : ae_fin_strongly_measurable f μ :=
  (mem_ℒp_one_iff_integrable.mpr hf).AeFinStronglyMeasurable one_ne_zero Ennreal.coe_ne_top

theorem Lp.fin_strongly_measurable (f : Lp G p μ) (hp_ne_zero : p ≠ 0) (hp_ne_top : p ≠ ∞) :
    fin_strongly_measurable f μ :=
  (Lp.mem_ℒp f).fin_strongly_measurable_of_measurable (Lp.measurable f) hp_ne_zero hp_ne_top

end MeasureTheory

