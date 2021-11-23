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

variable{α E :
    Type
      _}[MeasurableSpace
      α]{μ :
    Measureₓ
      α}[NormedGroup
      E][NormedSpace ℝ E][CompleteSpace E][TopologicalSpace.SecondCountableTopology E][MeasurableSpace E][BorelSpace E]

-- error in Analysis.Convex.Integral: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
private
theorem convex.smul_integral_mem_of_measurable
[is_finite_measure μ]
{s : set E}
(hs : convex exprℝ() s)
(hsc : is_closed s)
(hμ : «expr ≠ »(μ, 0))
{f : α → E}
(hfs : «expr∀ᵐ ∂ , »((x), μ, «expr ∈ »(f x, s)))
(hfi : integrable f μ)
(hfm : measurable f) : «expr ∈ »(«expr • »(«expr ⁻¹»((μ univ).to_real), «expr∫ , ∂ »((x), f x, μ)), s) :=
begin
  unfreezingI { rcases [expr eq_empty_or_nonempty s, "with", ident rfl, "|", "⟨", ident y₀, ",", ident h₀, "⟩"] },
  { refine [expr (hμ _).elim],
    simpa [] [] [] [] [] ["using", expr hfs] },
  rw ["<-", expr hsc.closure_eq] ["at", ident hfs],
  have [ident hc] [":", expr integrable (λ _, y₀) μ] [":=", expr integrable_const _],
  set [] [ident F] [":", expr exprℕ() → simple_func α E] [":="] [expr simple_func.approx_on f hfm s y₀ h₀] [],
  have [] [":", expr tendsto (λ n, (F n).integral μ) at_top «expr $ »(expr𝓝(), «expr∫ , ∂ »((x), f x, μ))] [],
  { simp [] [] ["only"] ["[", expr simple_func.integral_eq_integral _ (simple_func.integrable_approx_on hfm hfi h₀ hc _), "]"] [] [],
    exact [expr tendsto_integral_of_L1 _ hfi «expr $ »(eventually_of_forall, simple_func.integrable_approx_on hfm hfi h₀ hc) (simple_func.tendsto_approx_on_L1_nnnorm hfm h₀ hfs (hfi.sub hc).2)] },
  refine [expr hsc.mem_of_tendsto (tendsto_const_nhds.smul this) «expr $ »(eventually_of_forall, λ n, _)],
  have [] [":", expr «expr = »(«expr∑ in , »((y), (F n).range, (μ «expr ⁻¹' »(F n, {y})).to_real), (μ univ).to_real)] [],
  by rw ["[", "<-", expr (F n).sum_range_measure_preimage_singleton, ",", expr @ennreal.to_real_sum _ _ (λ
    y, μ «expr ⁻¹' »(F n, {y})) (λ _ _, measure_ne_top _ _), "]"] [],
  rw ["[", "<-", expr this, ",", expr simple_func.integral, "]"] [],
  refine [expr hs.center_mass_mem (λ _ _, ennreal.to_real_nonneg) _ _],
  { rw ["[", expr this, ",", expr ennreal.to_real_pos_iff, ",", expr pos_iff_ne_zero, ",", expr ne.def, ",", expr measure.measure_univ_eq_zero, "]"] [],
    exact [expr ⟨hμ, measure_ne_top _ _⟩] },
  { simp [] [] ["only"] ["[", expr simple_func.mem_range, "]"] [] [],
    rintros ["_", "⟨", ident x, ",", ident rfl, "⟩"],
    exact [expr simple_func.approx_on_mem hfm h₀ n x] }
end

-- error in Analysis.Convex.Integral: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- If `μ` is a non-zero finite measure on `α`, `s` is a convex closed set in `E`, and `f` is an
integrable function sending `μ`-a.e. points to `s`, then the average value of `f` belongs to `s`:
`(μ univ).to_real⁻¹ • ∫ x, f x ∂μ ∈ s`. See also `convex.center_mass_mem` for a finite sum version
of this lemma. -/
theorem convex.smul_integral_mem
[is_finite_measure μ]
{s : set E}
(hs : convex exprℝ() s)
(hsc : is_closed s)
(hμ : «expr ≠ »(μ, 0))
{f : α → E}
(hfs : «expr∀ᵐ ∂ , »((x), μ, «expr ∈ »(f x, s)))
(hfi : integrable f μ) : «expr ∈ »(«expr • »(«expr ⁻¹»((μ univ).to_real), «expr∫ , ∂ »((x), f x, μ)), s) :=
begin
  have [] [":", expr «expr∀ᵐ ∂ , »((x : α), μ, «expr ∈ »(hfi.ae_measurable.mk f x, s))] [],
  { filter_upwards ["[", expr hfs, ",", expr hfi.ae_measurable.ae_eq_mk, "]"] [],
    assume [binders (a ha h)],
    rwa ["<-", expr h] [] },
  convert [] [expr convex.smul_integral_mem_of_measurable hs hsc hμ this (hfi.congr hfi.ae_measurable.ae_eq_mk) hfi.ae_measurable.measurable_mk] ["using", 2],
  apply [expr integral_congr_ae],
  exact [expr hfi.ae_measurable.ae_eq_mk]
end

/-- If `μ` is a probability measure on `α`, `s` is a convex closed set in `E`, and `f` is an
integrable function sending `μ`-a.e. points to `s`, then the expected value of `f` belongs to `s`:
`∫ x, f x ∂μ ∈ s`. See also `convex.sum_mem` for a finite sum version of this lemma. -/
theorem Convex.integral_mem [is_probability_measure μ] {s : Set E} (hs : Convex ℝ s) (hsc : IsClosed s) {f : α → E}
  (hf : ∀ᵐx ∂μ, f x ∈ s) (hfi : integrable f μ) : (∫x, f x ∂μ) ∈ s :=
  by 
    simpa [measure_univ] using hs.smul_integral_mem hsc (is_probability_measure.ne_zero μ) hf hfi

-- error in Analysis.Convex.Integral: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Jensen's inequality: if a function `g : E → ℝ` is convex and continuous on a convex closed set
`s`, `μ` is a finite non-zero measure on `α`, and `f : α → E` is a function sending `μ`-a.e. points
to `s`, then the value of `g` at the average value of `f` is less than or equal to the average value
of `g ∘ f` provided that both `f` and `g ∘ f` are integrable. See also `convex.map_center_mass_le`
for a finite sum version of this lemma. -/
theorem convex_on.map_smul_integral_le
[is_finite_measure μ]
{s : set E}
{g : E → exprℝ()}
(hg : convex_on exprℝ() s g)
(hgc : continuous_on g s)
(hsc : is_closed s)
(hμ : «expr ≠ »(μ, 0))
{f : α → E}
(hfs : «expr∀ᵐ ∂ , »((x), μ, «expr ∈ »(f x, s)))
(hfi : integrable f μ)
(hgi : integrable «expr ∘ »(g, f) μ) : «expr ≤ »(g «expr • »(«expr ⁻¹»((μ univ).to_real), «expr∫ , ∂ »((x), f x, μ)), «expr • »(«expr ⁻¹»((μ univ).to_real), «expr∫ , ∂ »((x), g (f x), μ))) :=
begin
  set [] [ident t] [] [":="] [expr {p : «expr × »(E, exprℝ()) | «expr ∧ »(«expr ∈ »(p.1, s), «expr ≤ »(g p.1, p.2))}] [],
  have [ident ht_conv] [":", expr convex exprℝ() t] [":=", expr hg.convex_epigraph],
  have [ident ht_closed] [":", expr is_closed t] [":=", expr (hsc.preimage continuous_fst).is_closed_le (hgc.comp continuous_on_fst (subset.refl _)) continuous_on_snd],
  have [ident ht_mem] [":", expr «expr∀ᵐ ∂ , »((x), μ, «expr ∈ »((f x, g (f x)), t))] [":=", expr hfs.mono (λ
    x hx, ⟨hx, le_rfl⟩)],
  simpa [] [] [] ["[", expr integral_pair hfi hgi, "]"] [] ["using", expr (ht_conv.smul_integral_mem ht_closed hμ ht_mem (hfi.prod_mk hgi)).2]
end

/-- Convex **Jensen's inequality**: if a function `g : E → ℝ` is convex and continuous on a convex
closed set `s`, `μ` is a probability measure on `α`, and `f : α → E` is a function sending `μ`-a.e.
points to `s`, then the value of `g` at the expected value of `f` is less than or equal to the
expected value of `g ∘ f` provided that both `f` and `g ∘ f` are integrable. See also
`convex_on.map_center_mass_le` for a finite sum version of this lemma. -/
theorem ConvexOn.map_integral_le [is_probability_measure μ] {s : Set E} {g : E → ℝ} (hg : ConvexOn ℝ s g)
  (hgc : ContinuousOn g s) (hsc : IsClosed s) {f : α → E} (hfs : ∀ᵐx ∂μ, f x ∈ s) (hfi : integrable f μ)
  (hgi : integrable (g ∘ f) μ) : g (∫x, f x ∂μ) ≤ ∫x, g (f x) ∂μ :=
  by 
    simpa [measure_univ] using hg.map_smul_integral_le hgc hsc (is_probability_measure.ne_zero μ) hfs hfi hgi

