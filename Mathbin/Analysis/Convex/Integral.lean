import Mathbin.Analysis.Convex.Function
import Mathbin.MeasureTheory.Integral.SetIntegral

/-!
# Jensen's inequality for integrals

In this file we prove four theorems:

* `convex.smul_integral_mem`: if `μ` is a non-zero finite measure on `α`, `s` is a convex closed set
  in `E`, and `f` is an integrable function sending `μ`-a.e. points to `s`, then the average value
  of `f` belongs to `s`: `(μ univ).to_real⁻¹ • ∫ x, f x ∂μ ∈ s`. See also `convex.center_mass_mem`
  for a finite sum version of this lemma.

* `convex.integral_mem`: if `μ` is a probability measure on `α`, `s` is a convex closed set in `E`,
  and `f` is an integrable function sending `μ`-a.e. points to `s`, then the expected value of `f`
  belongs to `s`: `∫ x, f x ∂μ ∈ s`. See also `convex.sum_mem` for a finite sum version of this
  lemma.

* `convex_on.map_smul_integral_le`: Convex Jensen's inequality: If a function `g : E → ℝ` is convex
  and continuous on a convex closed set `s`, `μ` is a finite non-zero measure on `α`, and
  `f : α → E` is a function sending `μ`-a.e. points to `s`, then the value of `g` at the average
  value of `f` is less than or equal to the average value of `g ∘ f` provided that both `f` and
  `g ∘ f` are integrable. See also `convex_on.map_sum_le` for a finite sum version of this lemma.

* `convex_on.map_integral_le`: Convex Jensen's inequality: If a function `g : E → ℝ` is convex and
  continuous on a convex closed set `s`, `μ` is a probability measure on `α`, and `f : α → E` is a
  function sending `μ`-a.e. points to `s`, then the value of `g` at the expected value of `f` is
  less than or equal to the expected value of `g ∘ f` provided that both `f` and `g ∘ f` are
  integrable. See also `convex_on.map_sum_le` for a finite sum version of this lemma.

## Tags

convex, integral, center mass, Jensen's inequality
-/


open MeasureTheory Set Filter

open_locale TopologicalSpace BigOperators

variable {α E : Type _} [MeasurableSpace α] {μ : Measureₓ α} [NormedGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [TopologicalSpace.SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E]

private theorem convex.smul_integral_mem_of_measurable [IsFiniteMeasure μ] {s : Set E} (hs : Convex ℝ s)
    (hsc : IsClosed s) (hμ : μ ≠ 0) {f : α → E} (hfs : ∀ᵐ x ∂μ, f x ∈ s) (hfi : Integrable f μ) (hfm : Measurable f) :
    ((μ Univ).toReal⁻¹ • ∫ x, f x ∂μ) ∈ s := by
  rcases eq_empty_or_nonempty s with (rfl | ⟨y₀, h₀⟩)
  · refine' (hμ _).elim
    simpa using hfs
    
  rw [← hsc.closure_eq] at hfs
  have hc : integrable (fun _ => y₀) μ := integrable_const _
  set F : ℕ → simple_func α E := simple_func.approx_on f hfm s y₀ h₀
  have : tendsto (fun n => (F n).integral μ) at_top (𝓝 <| ∫ x, f x ∂μ) := by
    simp only [simple_func.integral_eq_integral _ (simple_func.integrable_approx_on hfm hfi h₀ hc _)]
    exact
      tendsto_integral_of_L1 _ hfi (eventually_of_forall <| simple_func.integrable_approx_on hfm hfi h₀ hc)
        (simple_func.tendsto_approx_on_L1_nnnorm hfm h₀ hfs (hfi.sub hc).2)
  refine' hsc.mem_of_tendsto (tendsto_const_nhds.smul this) (eventually_of_forall fun n => _)
  have : (∑ y in (F n).range, (μ (F n ⁻¹' {y})).toReal) = (μ univ).toReal := by
    rw [← (F n).sum_range_measure_preimage_singleton,
      @Ennreal.to_real_sum _ _ (fun y => μ (F n ⁻¹' {y})) fun _ _ => measure_ne_top _ _]
  rw [← this, simple_func.integral]
  refine' hs.center_mass_mem (fun _ _ => Ennreal.to_real_nonneg) _ _
  · rw [this]
    exact Ennreal.to_real_pos (mt measure.measure_univ_eq_zero.mp hμ) (measure_ne_top _ _)
    
  · simp only [simple_func.mem_range]
    rintro _ ⟨x, rfl⟩
    exact simple_func.approx_on_mem hfm h₀ n x
    

/-- If `μ` is a non-zero finite measure on `α`, `s` is a convex closed set in `E`, and `f` is an
integrable function sending `μ`-a.e. points to `s`, then the average value of `f` belongs to `s`:
`(μ univ).to_real⁻¹ • ∫ x, f x ∂μ ∈ s`. See also `convex.center_mass_mem` for a finite sum version
of this lemma. -/
theorem Convex.smul_integral_mem [IsFiniteMeasure μ] {s : Set E} (hs : Convex ℝ s) (hsc : IsClosed s) (hμ : μ ≠ 0)
    {f : α → E} (hfs : ∀ᵐ x ∂μ, f x ∈ s) (hfi : Integrable f μ) : ((μ Univ).toReal⁻¹ • ∫ x, f x ∂μ) ∈ s := by
  have : ∀ᵐ x : α ∂μ, hfi.ae_measurable.mk f x ∈ s := by
    filter_upwards [hfs, hfi.ae_measurable.ae_eq_mk] with _ _ h
    rwa [← h]
  convert
    convex.smul_integral_mem_of_measurable hs hsc hμ this (hfi.congr hfi.ae_measurable.ae_eq_mk)
      hfi.ae_measurable.measurable_mk using
    2
  apply integral_congr_ae
  exact hfi.ae_measurable.ae_eq_mk

/-- If `μ` is a probability measure on `α`, `s` is a convex closed set in `E`, and `f` is an
integrable function sending `μ`-a.e. points to `s`, then the expected value of `f` belongs to `s`:
`∫ x, f x ∂μ ∈ s`. See also `convex.sum_mem` for a finite sum version of this lemma. -/
theorem Convex.integral_mem [IsProbabilityMeasure μ] {s : Set E} (hs : Convex ℝ s) (hsc : IsClosed s) {f : α → E}
    (hf : ∀ᵐ x ∂μ, f x ∈ s) (hfi : Integrable f μ) : (∫ x, f x ∂μ) ∈ s := by
  simpa [measure_univ] using hs.smul_integral_mem hsc (is_probability_measure.ne_zero μ) hf hfi

/-- Jensen's inequality: if a function `g : E → ℝ` is convex and continuous on a convex closed set
`s`, `μ` is a finite non-zero measure on `α`, and `f : α → E` is a function sending `μ`-a.e. points
to `s`, then the value of `g` at the average value of `f` is less than or equal to the average value
of `g ∘ f` provided that both `f` and `g ∘ f` are integrable. See also `convex.map_center_mass_le`
for a finite sum version of this lemma. -/
theorem ConvexOn.map_smul_integral_le [IsFiniteMeasure μ] {s : Set E} {g : E → ℝ} (hg : ConvexOn ℝ s g)
    (hgc : ContinuousOn g s) (hsc : IsClosed s) (hμ : μ ≠ 0) {f : α → E} (hfs : ∀ᵐ x ∂μ, f x ∈ s) (hfi : Integrable f μ)
    (hgi : Integrable (g ∘ f) μ) : g ((μ Univ).toReal⁻¹ • ∫ x, f x ∂μ) ≤ (μ Univ).toReal⁻¹ • ∫ x, g (f x) ∂μ := by
  set t := { p : E × ℝ | p.1 ∈ s ∧ g p.1 ≤ p.2 }
  have ht_conv : Convex ℝ t := hg.convex_epigraph
  have ht_closed : IsClosed t :=
    (hsc.preimage continuous_fst).is_closed_le (hgc.comp continuous_on_fst (subset.refl _)) continuous_on_snd
  have ht_mem : ∀ᵐ x ∂μ, (f x, g (f x)) ∈ t := hfs.mono fun x hx => ⟨hx, le_rfl⟩
  simpa [integral_pair hfi hgi] using (ht_conv.smul_integral_mem ht_closed hμ ht_mem (hfi.prod_mk hgi)).2

/-- Convex **Jensen's inequality**: if a function `g : E → ℝ` is convex and continuous on a convex
closed set `s`, `μ` is a probability measure on `α`, and `f : α → E` is a function sending `μ`-a.e.
points to `s`, then the value of `g` at the expected value of `f` is less than or equal to the
expected value of `g ∘ f` provided that both `f` and `g ∘ f` are integrable. See also
`convex_on.map_center_mass_le` for a finite sum version of this lemma. -/
theorem ConvexOn.map_integral_le [IsProbabilityMeasure μ] {s : Set E} {g : E → ℝ} (hg : ConvexOn ℝ s g)
    (hgc : ContinuousOn g s) (hsc : IsClosed s) {f : α → E} (hfs : ∀ᵐ x ∂μ, f x ∈ s) (hfi : Integrable f μ)
    (hgi : Integrable (g ∘ f) μ) : g (∫ x, f x ∂μ) ≤ ∫ x, g (f x) ∂μ := by
  simpa [measure_univ] using hg.map_smul_integral_le hgc hsc (is_probability_measure.ne_zero μ) hfs hfi hgi

