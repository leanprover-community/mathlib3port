import Mathbin.MeasureTheory.Covering.VitaliFamily 
import Mathbin.MeasureTheory.Measure.Regular 
import Mathbin.MeasureTheory.Function.AeMeasurableOrder 
import Mathbin.MeasureTheory.Integral.Lebesgue 
import Mathbin.MeasureTheory.Decomposition.RadonNikodym

/-!
# Differentiation of measures

On a metric space with a measure `μ`, consider a Vitali family (i.e., for each `x` one has a family
of sets shrinking to `x`, with a good behavior with respect to covering theorems).
Consider also another measure `ρ`. Then, for almost every `x`, the ratio `ρ a / μ a` converges when
`a` shrinks to `x` along the Vitali family, towards the Radon-Nikodym derivative of `ρ` with
respect to `μ`. This is the main theorem on differentiation of measures.

This theorem is proved in this file, under the name `vitali_family.ae_tendsto_rn_deriv`. Note that,
almost surely, `μ a` is eventually positive and finite (see
`vitali_family.ae_eventually_measure_pos` and `vitali_family.eventually_measure_lt_top`), so the
ratio really makes sense.

For concrete applications, one needs concrete instances of Vitali families, as provided for instance
by `besicovitch.vitali_family` (for balls) or by `vitali.vitali_family` (for doubling measures).

## Sketch of proof

Let `v` be a Vitali family for `μ`. Assume for simplicity that `ρ` is absolutely continuous with
respect to `μ`, as the case of a singular measure is easier.

It is easy to see that a set `s` on which `liminf ρ a / μ a < q` satisfies `ρ s ≤ q * μ s`, by using
a disjoint subcovering provided by the definition of Vitali families. Similarly for the limsup.
It follows that a set on which `ρ a / μ a` oscillates has measure `0`, and therefore that
`ρ a / μ a` converges almost surely (`vitali_family.ae_tendsto_div`). Moreover, on a set where the
limit is close to a constant `c`, one gets `ρ s ∼ c μ s`, using again a covering lemma as above.
It follows that `ρ` is equal to `μ.with_density (v.lim_ratio ρ x)`, where `v.lim_ratio ρ x` is the
limit of `ρ a / μ a` at `x` (which is well defined almost everywhere). By uniqueness of the
Radon-Nikodym derivative, one gets `v.lim_ratio ρ x = ρ.rn_deriv μ x` almost everywhere, completing
the proof.

There is a difficulty in this sketch: this argument works well when `v.lim_ratio ρ` is measurable,
but there is no guarantee that this is the case, especially if one doesn't make further assumptions
on the Vitali family. We use an indirect argument to show that `v.lim_ratio ρ` is always
almost everywhere measurable, again based on the disjoint subcovering argument
(see `vitali_family.exists_measurable_supersets_lim_ratio`), and then proceed as sketched above
but replacing `v.lim_ratio ρ` by a measurable version called `v.lim_ratio_meas ρ`.

## References

* [Herbert Federer, Geometric Measure Theory, Chapter 2.9][Federer1996]
-/


open MeasureTheory Metric Set Filter TopologicalSpace MeasureTheory.Measure

open_locale Filter Ennreal MeasureTheory Nnreal TopologicalSpace

attribute [local instance] Emetric.second_countable_of_sigma_compact

variable{α : Type _}[MetricSpace α]{m0 : MeasurableSpace α}{μ : Measureₓ α}(v : VitaliFamily μ)

include v

namespace VitaliFamily

/-- The limit along a Vitali family of `ρ a / μ a` where it makes sense, and garbage otherwise.
Do *not* use this definition: it is only a temporary device to show that this ratio tends almost
everywhere to the Radon-Nikodym derivative. -/
noncomputable def lim_ratio (ρ : Measureₓ α) (x : α) : ℝ≥0∞ :=
  limₓ (v.filter_at x) fun a => ρ a / μ a

-- error in MeasureTheory.Covering.Differentiation: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- For almost every point `x`, sufficiently small sets in a Vitali family around `x` have positive
measure. (This is a nontrivial result, following from the covering property of Vitali families). -/
theorem ae_eventually_measure_pos
[second_countable_topology α] : «expr∀ᵐ ∂ , »((x), μ, «expr∀ᶠ in , »((a), v.filter_at x, «expr < »(0, μ a))) :=
begin
  set [] [ident s] [] [":="] [expr {x | «expr¬ »(«expr∀ᶠ in , »((a), v.filter_at x, «expr < »(0, μ a)))}] ["with", ident hs],
  simp [] [] ["only"] ["[", expr not_lt, ",", expr not_eventually, ",", expr nonpos_iff_eq_zero, "]"] [] ["at", ident hs],
  change [expr «expr = »(μ s, 0)] [] [],
  let [ident f] [":", expr α → set (set α)] [":=", expr λ x, {a | «expr = »(μ a, 0)}],
  have [ident h] [":", expr v.fine_subfamily_on f s] [],
  { assume [binders (x hx ε εpos)],
    rw [expr hs] ["at", ident hx],
    simp [] [] ["only"] ["[", expr frequently_filter_at_iff, ",", expr exists_prop, ",", expr gt_iff_lt, ",", expr mem_set_of_eq, "]"] [] ["at", ident hx],
    rcases [expr hx ε εpos, "with", "⟨", ident a, ",", ident a_sets, ",", ident ax, ",", ident μa, "⟩"],
    exact [expr ⟨a, ⟨a_sets, μa⟩, ax⟩] },
  refine [expr le_antisymm _ bot_le],
  calc
    «expr ≤ »(μ s, «expr∑' , »((x : h.index), μ (h.covering x))) : h.measure_le_tsum
    «expr = »(..., «expr∑' , »((x : h.index), 0)) : by { congr,
      ext1 [] [ident x],
      exact [expr h.covering_mem x.2] }
    «expr = »(..., 0) : by simp [] [] ["only"] ["[", expr tsum_zero, ",", expr add_zero, "]"] [] []
end

/-- For every point `x`, sufficiently small sets in a Vitali family around `x` have finite measure.
(This is a trivial result, following from the fact that the measure is locally finite). -/
theorem eventually_measure_lt_top [is_locally_finite_measure μ] (x : α) : ∀ᶠa in v.filter_at x, μ a < ∞ :=
  by 
    obtain ⟨ε, εpos, με⟩ : ∃ (ε : ℝ)(hi : 0 < ε), μ (closed_ball x ε) < ∞ :=
      (μ.finite_at_nhds x).exists_mem_basis nhds_basis_closed_ball 
    exact v.eventually_filter_at_iff.2 ⟨ε, εpos, fun a ha haε => (measure_mono haε).trans_lt με⟩

-- error in MeasureTheory.Covering.Differentiation: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- If two measures `ρ` and `ν` have, at every point of a set `s`, arbitrarily small sets in a
Vitali family satisfying `ρ a ≤ ν a`, then `ρ s ≤ ν s` if `ρ ≪ μ`.-/
theorem measure_le_of_frequently_le
[sigma_compact_space α]
[borel_space α]
{ρ : measure α}
(ν : measure α)
[is_locally_finite_measure ν]
(hρ : «expr ≪ »(ρ, μ))
(s : set α)
(hs : ∀ x «expr ∈ » s, «expr∃ᶠ in , »((a), v.filter_at x, «expr ≤ »(ρ a, ν a))) : «expr ≤ »(ρ s, ν s) :=
begin
  apply [expr ennreal.le_of_forall_pos_le_add (λ ε εpos hc, _)],
  obtain ["⟨", ident U, ",", ident sU, ",", ident U_open, ",", ident νU, "⟩", ":", expr «expr∃ , »((U : set α)
    (H : «expr ⊆ »(s, U)), «expr ∧ »(is_open U, «expr ≤ »(ν U, «expr + »(ν s, ε)))), ":=", expr exists_is_open_le_add s ν (ennreal.coe_pos.2 εpos).ne'],
  let [ident f] [":", expr α → set (set α)] [":=", expr λ x, {a | «expr ∧ »(«expr ≤ »(ρ a, ν a), «expr ⊆ »(a, U))}],
  have [ident h] [":", expr v.fine_subfamily_on f s] [],
  { apply [expr v.fine_subfamily_on_of_frequently f s (λ x hx, _)],
    have [] [] [":=", expr (hs x hx).and_eventually ((v.eventually_filter_at_mem_sets x).and (v.eventually_filter_at_subset_of_nhds (U_open.mem_nhds (sU hx))))],
    apply [expr frequently.mono this],
    rintros [ident a, "⟨", ident ρa, ",", ident av, ",", ident aU, "⟩"],
    exact [expr ⟨ρa, aU⟩] },
  haveI [] [":", expr encodable h.index] [":=", expr h.index_countable.to_encodable],
  calc
    «expr ≤ »(ρ s, «expr∑' , »((x : h.index), ρ (h.covering x))) : h.measure_le_tsum_of_absolutely_continuous hρ
    «expr ≤ »(..., «expr∑' , »((x : h.index), ν (h.covering x))) : ennreal.tsum_le_tsum (λ x, (h.covering_mem x.2).1)
    «expr = »(..., ν «expr⋃ , »((x : h.index), h.covering x)) : by rw ["[", expr measure_Union h.covering_disjoint_subtype (λ
      i, h.measurable_set_u i.2), "]"] []
    «expr ≤ »(..., ν U) : measure_mono (Union_subset (λ i, (h.covering_mem i.2).2))
    «expr ≤ »(..., «expr + »(ν s, ε)) : νU
end

section 

variable[SigmaCompactSpace α][BorelSpace α][is_locally_finite_measure μ]{ρ : Measureₓ α}[is_locally_finite_measure ρ]

-- error in MeasureTheory.Covering.Differentiation: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- If a measure `ρ` is singular with respect to `μ`, then for `μ` almost every `x`, the ratio
`ρ a / μ a` tends to zero when `a` shrinks to `x` along the Vitali family. This makes sense
as `μ a` is eventually positive by `ae_eventually_measure_pos`. -/
theorem ae_eventually_measure_zero_of_singular
(hρ : «expr ⊥ₘ »(ρ, μ)) : «expr∀ᵐ ∂ , »((x), μ, tendsto (λ a, «expr / »(ρ a, μ a)) (v.filter_at x) (expr𝓝() 0)) :=
begin
  have [ident A] [":", expr ∀
   ε «expr > » (0 : «exprℝ≥0»()), «expr∀ᵐ ∂ , »((x), μ, «expr∀ᶠ in , »((a), v.filter_at x, «expr < »(ρ a, «expr * »(ε, μ a))))] [],
  { assume [binders (ε εpos)],
    set [] [ident s] [] [":="] [expr {x | «expr¬ »(«expr∀ᶠ in , »((a), v.filter_at x, «expr < »(ρ a, «expr * »(ε, μ a))))}] ["with", ident hs],
    change [expr «expr = »(μ s, 0)] [] [],
    obtain ["⟨", ident o, ",", ident o_meas, ",", ident ρo, ",", ident μo, "⟩", ":", expr «expr∃ , »((o : set α), «expr ∧ »(measurable_set o, «expr ∧ »(«expr = »(ρ o, 0), «expr = »(μ «expr ᶜ»(o), 0)))), ":=", expr hρ],
    apply [expr le_antisymm _ bot_le],
    calc
      «expr ≤ »(μ s, μ «expr ∪ »(«expr ∩ »(s, o), «expr ᶜ»(o))) : begin
        conv_lhs [] [] { rw ["<-", expr inter_union_compl s o] },
        exact [expr measure_mono (union_subset_union_right _ (inter_subset_right _ _))]
      end
      «expr ≤ »(..., «expr + »(μ «expr ∩ »(s, o), μ «expr ᶜ»(o))) : measure_union_le _ _
      «expr = »(..., μ «expr ∩ »(s, o)) : by rw ["[", expr μo, ",", expr add_zero, "]"] []
      «expr = »(..., «expr * »(«expr ⁻¹»(ε), «expr • »(ε, μ) «expr ∩ »(s, o))) : begin
        simp [] [] ["only"] ["[", expr coe_nnreal_smul_apply, ",", "<-", expr mul_assoc, ",", expr mul_comm _ (ε : «exprℝ≥0∞»()), "]"] [] [],
        rw ["[", expr ennreal.mul_inv_cancel (ennreal.coe_pos.2 εpos).ne' ennreal.coe_ne_top, ",", expr one_mul, "]"] []
      end
      «expr ≤ »(..., «expr * »(«expr ⁻¹»(ε), ρ «expr ∩ »(s, o))) : begin
        apply [expr ennreal.mul_le_mul le_rfl],
        refine [expr v.measure_le_of_frequently_le ρ ((measure.absolutely_continuous.refl μ).smul ε) _ _],
        assume [binders (x hx)],
        rw [expr hs] ["at", ident hx],
        simp [] [] ["only"] ["[", expr mem_inter_eq, ",", expr not_lt, ",", expr not_eventually, ",", expr mem_set_of_eq, "]"] [] ["at", ident hx],
        exact [expr hx.1]
      end
      «expr ≤ »(..., «expr * »(«expr ⁻¹»(ε), ρ o)) : ennreal.mul_le_mul le_rfl (measure_mono (inter_subset_right _ _))
      «expr = »(..., 0) : by rw ["[", expr ρo, ",", expr mul_zero, "]"] [] },
  obtain ["⟨", ident u, ",", ident u_anti, ",", ident u_pos, ",", ident u_lim, "⟩", ":", expr «expr∃ , »((u : exprℕ() → «exprℝ≥0»()), «expr ∧ »(strict_anti u, «expr ∧ »(∀
      n : exprℕ(), «expr < »(0, u n), tendsto u at_top (expr𝓝() 0)))), ":=", expr exists_seq_strict_anti_tendsto (0 : «exprℝ≥0»())],
  have [ident B] [":", expr «expr∀ᵐ ∂ , »((x), μ, ∀
    n, «expr∀ᶠ in , »((a), v.filter_at x, «expr < »(ρ a, «expr * »(u n, μ a))))] [":=", expr ae_all_iff.2 (λ
    n, A (u n) (u_pos n))],
  filter_upwards ["[", expr B, ",", expr v.ae_eventually_measure_pos, "]"] [],
  assume [binders (x hx h'x)],
  refine [expr tendsto_order.2 ⟨λ z hz, (ennreal.not_lt_zero hz).elim, λ z hz, _⟩],
  obtain ["⟨", ident w, ",", ident w_pos, ",", ident w_lt, "⟩", ":", expr «expr∃ , »((w : «exprℝ≥0»()), «expr ∧ »(«expr < »((0 : «exprℝ≥0∞»()), w), «expr < »((w : «exprℝ≥0∞»()), z))), ":=", expr ennreal.lt_iff_exists_nnreal_btwn.1 hz],
  obtain ["⟨", ident n, ",", ident hn, "⟩", ":", expr «expr∃ , »((n), «expr < »(u n, w)), ":=", expr ((tendsto_order.1 u_lim).2 w (ennreal.coe_pos.1 w_pos)).exists],
  filter_upwards ["[", expr hx n, ",", expr h'x, ",", expr v.eventually_measure_lt_top x, "]"] [],
  assume [binders (a ha μa_pos μa_lt_top)],
  rw [expr ennreal.div_lt_iff (or.inl μa_pos.ne') (or.inl μa_lt_top.ne)] [],
  exact [expr ha.trans_le (ennreal.mul_le_mul ((ennreal.coe_le_coe.2 hn.le).trans w_lt.le) le_rfl)]
end

section AbsolutelyContinuous

variable(hρ : ρ ≪ μ)

include hρ

/-- A set of points `s` satisfying both `ρ a ≤ c * μ a` and `ρ a ≥ d * μ a` at arbitrarily small
sets in a Vitali family has measure `0` if `c < d`. Indeed, the first inequality should imply
that `ρ s ≤ c * μ s`, and the second one that `ρ s ≥ d * μ s`, a contradiction if `0 < μ s`. -/
theorem null_of_frequently_le_of_frequently_ge {c d :  ℝ≥0 } (hcd : c < d) (s : Set α)
  (hc : ∀ x _ : x ∈ s, ∃ᶠa in v.filter_at x, ρ a ≤ c*μ a)
  (hd : ∀ x _ : x ∈ s, ∃ᶠa in v.filter_at x, ((d : ℝ≥0∞)*μ a) ≤ ρ a) : μ s = 0 :=
  by 
    apply null_of_locally_null s fun x hx => _ 
    obtain ⟨o, xo, o_open, μo⟩ : ∃ o : Set α, x ∈ o ∧ IsOpen o ∧ μ o < ∞ := measure.exists_is_open_measure_lt_top μ x 
    refine' ⟨o, mem_nhds_within_of_mem_nhds (o_open.mem_nhds xo), _⟩
    let s' := s ∩ o 
    byContra 
    apply lt_irreflₓ (ρ s')
    calc ρ s' ≤ c*μ s' := v.measure_le_of_frequently_le (c • μ) hρ s' fun x hx => hc x hx.1_ < d*μ s' :=
      by 
        apply (Ennreal.mul_lt_mul_right h _).2 (Ennreal.coe_lt_coe.2 hcd)
        exact (lt_of_le_of_ltₓ (measure_mono (inter_subset_right _ _)) μo).Ne _ ≤ ρ s' :=
      v.measure_le_of_frequently_le ρ ((measure.absolutely_continuous.refl μ).smul d) s' fun x hx => hd x hx.1

-- error in MeasureTheory.Covering.Differentiation: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- If `ρ` is absolutely continuous with respect to `μ`, then for almost every `x`,
the ratio `ρ a / μ a` converges as `a` shrinks to `x` along a Vitali family for `μ`. -/
theorem ae_tendsto_div : «expr∀ᵐ ∂ , »((x), μ, «expr∃ , »((c), tendsto (λ
   a, «expr / »(ρ a, μ a)) (v.filter_at x) (expr𝓝() c))) :=
begin
  obtain ["⟨", ident w, ",", ident w_count, ",", ident w_dense, ",", ident w_zero, ",", ident w_top, "⟩", ":", expr «expr∃ , »((w : set «exprℝ≥0∞»()), «expr ∧ »(countable w, «expr ∧ »(dense w, «expr ∧ »(«expr ∉ »(0, w), «expr ∉ »(«expr∞»(), w))))), ":=", expr ennreal.exists_countable_dense_no_zero_top],
  have [ident I] [":", expr ∀ x «expr ∈ » w, «expr ≠ »(x, «expr∞»())] [":=", expr λ x xs hx, w_top «expr ▸ »(hx, xs)],
  have [ident A] [":", expr ∀
   (c «expr ∈ » w)
   (d «expr ∈ » w), «expr < »(c, d) → «expr∀ᵐ ∂ , »((x), μ, «expr¬ »(«expr ∧ »(«expr∃ᶠ in , »((a), v.filter_at x, «expr < »(«expr / »(ρ a, μ a), c)), «expr∃ᶠ in , »((a), v.filter_at x, «expr < »(d, «expr / »(ρ a, μ a))))))] [],
  { assume [binders (c hc d hd hcd)],
    lift [expr c] ["to", expr «exprℝ≥0»()] ["using", expr I c hc] [],
    lift [expr d] ["to", expr «exprℝ≥0»()] ["using", expr I d hd] [],
    apply [expr v.null_of_frequently_le_of_frequently_ge hρ (ennreal.coe_lt_coe.1 hcd)],
    { simp [] [] ["only"] ["[", expr and_imp, ",", expr exists_prop, ",", expr not_frequently, ",", expr not_and, ",", expr not_lt, ",", expr not_le, ",", expr not_eventually, ",", expr mem_set_of_eq, ",", expr mem_compl_eq, ",", expr not_forall, "]"] [] [],
      assume [binders (x h1x h2x)],
      apply [expr h1x.mono (λ a ha, _)],
      refine [expr (ennreal.div_le_iff_le_mul _ (or.inr (bot_le.trans_lt ha).ne')).1 ha.le],
      simp [] [] ["only"] ["[", expr ennreal.coe_ne_top, ",", expr ne.def, ",", expr or_true, ",", expr not_false_iff, "]"] [] [] },
    { simp [] [] ["only"] ["[", expr and_imp, ",", expr exists_prop, ",", expr not_frequently, ",", expr not_and, ",", expr not_lt, ",", expr not_le, ",", expr not_eventually, ",", expr mem_set_of_eq, ",", expr mem_compl_eq, ",", expr not_forall, "]"] [] [],
      assume [binders (x h1x h2x)],
      apply [expr h2x.mono (λ a ha, _)],
      exact [expr ennreal.mul_le_of_le_div ha.le] } },
  have [ident B] [":", expr «expr∀ᵐ ∂ , »((x), μ, ∀
    (c «expr ∈ » w)
    (d «expr ∈ » w), «expr < »(c, d) → «expr¬ »(«expr ∧ »(«expr∃ᶠ in , »((a), v.filter_at x, «expr < »(«expr / »(ρ a, μ a), c)), «expr∃ᶠ in , »((a), v.filter_at x, «expr < »(d, «expr / »(ρ a, μ a))))))] [],
  by simpa [] [] ["only"] ["[", expr ae_ball_iff w_count, ",", expr ae_imp_iff, "]"] [] [],
  filter_upwards ["[", expr B, "]"] [],
  assume [binders (x hx)],
  exact [expr tendsto_of_no_upcrossings w_dense hx]
end

theorem ae_tendsto_lim_ratio : ∀ᵐx ∂μ, tendsto (fun a => ρ a / μ a) (v.filter_at x) (𝓝 (v.lim_ratio ρ x)) :=
  by 
    filterUpwards [v.ae_tendsto_div hρ]
    intro x hx 
    exact tendsto_nhds_lim hx

-- error in MeasureTheory.Covering.Differentiation: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Given two thresholds `p < q`, the sets `{x | v.lim_ratio ρ x < p}`
and `{x | q < v.lim_ratio ρ x}` are obviously disjoint. The key to proving that `v.lim_ratio ρ` is
almost everywhere measurable is to show that these sets have measurable supersets which are also
disjoint, up to zero measure. This is the content of this lemma. -/
theorem exists_measurable_supersets_lim_ratio
{p q : «exprℝ≥0»()}
(hpq : «expr < »(p, q)) : «expr∃ , »((a
  b), «expr ∧ »(measurable_set a, «expr ∧ »(measurable_set b, «expr ∧ »(«expr ⊆ »({x | «expr < »(v.lim_ratio ρ x, p)}, a), «expr ∧ »(«expr ⊆ »({x | «expr < »((q : «exprℝ≥0∞»()), v.lim_ratio ρ x)}, b), «expr = »(μ «expr ∩ »(a, b), 0)))))) :=
begin
  let [ident s] [] [":=", expr {x | «expr∃ , »((c), tendsto (λ a, «expr / »(ρ a, μ a)) (v.filter_at x) (expr𝓝() c))}],
  let [ident o] [":", expr exprℕ() → set α] [":=", expr spanning_sets «expr + »(ρ, μ)],
  let [ident u] [] [":=", expr λ n, «expr ∩ »(«expr ∩ »(s, {x | «expr < »(v.lim_ratio ρ x, p)}), o n)],
  let [ident w] [] [":=", expr λ n, «expr ∩ »(«expr ∩ »(s, {x | «expr < »((q : «exprℝ≥0∞»()), v.lim_ratio ρ x)}), o n)],
  refine [expr ⟨«expr ∪ »(to_measurable μ «expr ᶜ»(s), «expr⋃ , »((n), to_measurable «expr + »(ρ, μ) (u n))), «expr ∪ »(to_measurable μ «expr ᶜ»(s), «expr⋃ , »((n), to_measurable «expr + »(ρ, μ) (w n))), _, _, _, _, _⟩],
  { exact [expr (measurable_set_to_measurable _ _).union (measurable_set.Union (λ
       n, measurable_set_to_measurable _ _))] },
  { exact [expr (measurable_set_to_measurable _ _).union (measurable_set.Union (λ
       n, measurable_set_to_measurable _ _))] },
  { assume [binders (x hx)],
    by_cases [expr h, ":", expr «expr ∈ »(x, s)],
    { refine [expr or.inr (mem_Union.2 ⟨spanning_sets_index «expr + »(ρ, μ) x, _⟩)],
      exact [expr subset_to_measurable _ _ ⟨⟨h, hx⟩, mem_spanning_sets_index _ _⟩] },
    { exact [expr or.inl (subset_to_measurable μ «expr ᶜ»(s) h)] } },
  { assume [binders (x hx)],
    by_cases [expr h, ":", expr «expr ∈ »(x, s)],
    { refine [expr or.inr (mem_Union.2 ⟨spanning_sets_index «expr + »(ρ, μ) x, _⟩)],
      exact [expr subset_to_measurable _ _ ⟨⟨h, hx⟩, mem_spanning_sets_index _ _⟩] },
    { exact [expr or.inl (subset_to_measurable μ «expr ᶜ»(s) h)] } },
  suffices [ident H] [":", expr ∀
   m n : exprℕ(), «expr = »(μ «expr ∩ »(to_measurable «expr + »(ρ, μ) (u m), to_measurable «expr + »(ρ, μ) (w n)), 0)],
  { have [ident A] [":", expr «expr ⊆ »(«expr ∩ »(«expr ∪ »(to_measurable μ «expr ᶜ»(s), «expr⋃ , »((n), to_measurable «expr + »(ρ, μ) (u n))), «expr ∪ »(to_measurable μ «expr ᶜ»(s), «expr⋃ , »((n), to_measurable «expr + »(ρ, μ) (w n)))), «expr ∪ »(to_measurable μ «expr ᶜ»(s), «expr⋃ , »((m
         n), «expr ∩ »(to_measurable «expr + »(ρ, μ) (u m), to_measurable «expr + »(ρ, μ) (w n)))))] [],
    { simp [] [] ["only"] ["[", expr inter_distrib_left, ",", expr inter_distrib_right, ",", expr true_and, ",", expr subset_union_left, ",", expr union_subset_iff, ",", expr inter_self, "]"] [] [],
      refine [expr ⟨_, _, _⟩],
      { exact [expr (inter_subset_left _ _).trans (subset_union_left _ _)] },
      { exact [expr (inter_subset_right _ _).trans (subset_union_left _ _)] },
      { simp_rw ["[", expr Union_inter, ",", expr inter_Union, "]"] [],
        exact [expr subset_union_right _ _] } },
    refine [expr le_antisymm ((measure_mono A).trans _) bot_le],
    calc
      «expr ≤ »(μ «expr ∪ »(to_measurable μ «expr ᶜ»(s), «expr⋃ , »((m
          n), «expr ∩ »(to_measurable «expr + »(ρ, μ) (u m), to_measurable «expr + »(ρ, μ) (w n)))), «expr + »(μ (to_measurable μ «expr ᶜ»(s)), μ «expr⋃ , »((m
          n), «expr ∩ »(to_measurable «expr + »(ρ, μ) (u m), to_measurable «expr + »(ρ, μ) (w n))))) : measure_union_le _ _
      «expr = »(..., μ «expr⋃ , »((m
         n), «expr ∩ »(to_measurable «expr + »(ρ, μ) (u m), to_measurable «expr + »(ρ, μ) (w n)))) : by { have [] [":", expr «expr = »(μ «expr ᶜ»(s), 0)] [":=", expr v.ae_tendsto_div hρ],
        rw ["[", expr measure_to_measurable, ",", expr this, ",", expr zero_add, "]"] [] }
      «expr ≤ »(..., «expr∑' , »((m
         n), μ «expr ∩ »(to_measurable «expr + »(ρ, μ) (u m), to_measurable «expr + »(ρ, μ) (w n)))) : (measure_Union_le _).trans (ennreal.tsum_le_tsum (λ
        m, measure_Union_le _))
      «expr = »(..., 0) : by simp [] [] ["only"] ["[", expr H, ",", expr tsum_zero, "]"] [] [] },
  assume [binders (m n)],
  have [ident I] [":", expr «expr ≠ »(«expr + »(ρ, μ) (u m), «expr∞»())] [],
  { apply [expr (lt_of_le_of_lt (measure_mono _) (measure_spanning_sets_lt_top «expr + »(ρ, μ) m)).ne],
    exact [expr inter_subset_right _ _] },
  have [ident J] [":", expr «expr ≠ »(«expr + »(ρ, μ) (w n), «expr∞»())] [],
  { apply [expr (lt_of_le_of_lt (measure_mono _) (measure_spanning_sets_lt_top «expr + »(ρ, μ) n)).ne],
    exact [expr inter_subset_right _ _] },
  have [ident A] [":", expr «expr ≤ »(ρ «expr ∩ »(to_measurable «expr + »(ρ, μ) (u m), to_measurable «expr + »(ρ, μ) (w n)), «expr * »(p, μ «expr ∩ »(to_measurable «expr + »(ρ, μ) (u m), to_measurable «expr + »(ρ, μ) (w n))))] [":=", expr calc
     «expr = »(ρ «expr ∩ »(to_measurable «expr + »(ρ, μ) (u m), to_measurable «expr + »(ρ, μ) (w n)), ρ «expr ∩ »(u m, to_measurable «expr + »(ρ, μ) (w n))) : measure_to_measurable_add_inter_left (measurable_set_to_measurable _ _) I
     «expr ≤ »(..., «expr • »(p, μ) «expr ∩ »(u m, to_measurable «expr + »(ρ, μ) (w n))) : begin
       refine [expr v.measure_le_of_frequently_le _ hρ _ (λ x hx, _)],
       have [ident L] [":", expr tendsto (λ
         a : set α, «expr / »(ρ a, μ a)) (v.filter_at x) (expr𝓝() (v.lim_ratio ρ x))] [":=", expr tendsto_nhds_lim hx.1.1.1],
       have [ident I] [":", expr «expr∀ᶠ in , »((b : set α), v.filter_at x, «expr < »(«expr / »(ρ b, μ b), p))] [":=", expr (tendsto_order.1 L).2 _ hx.1.1.2],
       apply [expr I.frequently.mono (λ a ha, _)],
       rw ["[", expr coe_nnreal_smul_apply, "]"] [],
       refine [expr (ennreal.div_le_iff_le_mul _ (or.inr (bot_le.trans_lt ha).ne')).1 ha.le],
       simp [] [] ["only"] ["[", expr ennreal.coe_ne_top, ",", expr ne.def, ",", expr or_true, ",", expr not_false_iff, "]"] [] []
     end
     «expr = »(..., «expr * »(p, μ «expr ∩ »(to_measurable «expr + »(ρ, μ) (u m), to_measurable «expr + »(ρ, μ) (w n)))) : by simp [] [] ["only"] ["[", expr coe_nnreal_smul_apply, ",", expr measure_to_measurable_add_inter_right (measurable_set_to_measurable _ _) I, "]"] [] []],
  have [ident B] [":", expr «expr ≤ »(«expr * »((q : «exprℝ≥0∞»()), μ «expr ∩ »(to_measurable «expr + »(ρ, μ) (u m), to_measurable «expr + »(ρ, μ) (w n))), ρ «expr ∩ »(to_measurable «expr + »(ρ, μ) (u m), to_measurable «expr + »(ρ, μ) (w n)))] [":=", expr calc
     «expr = »(«expr * »((q : «exprℝ≥0∞»()), μ «expr ∩ »(to_measurable «expr + »(ρ, μ) (u m), to_measurable «expr + »(ρ, μ) (w n))), «expr * »((q : «exprℝ≥0∞»()), μ «expr ∩ »(to_measurable «expr + »(ρ, μ) (u m), w n))) : begin
       conv_rhs [] [] { rw [expr inter_comm] },
       rw ["[", expr inter_comm, ",", expr measure_to_measurable_add_inter_right (measurable_set_to_measurable _ _) J, "]"] []
     end
     «expr ≤ »(..., ρ «expr ∩ »(to_measurable «expr + »(ρ, μ) (u m), w n)) : begin
       rw ["[", "<-", expr coe_nnreal_smul_apply, "]"] [],
       refine [expr v.measure_le_of_frequently_le _ (absolutely_continuous.rfl.coe_nnreal_smul _) _ _],
       assume [binders (x hx)],
       have [ident L] [":", expr tendsto (λ
         a : set α, «expr / »(ρ a, μ a)) (v.filter_at x) (expr𝓝() (v.lim_ratio ρ x))] [":=", expr tendsto_nhds_lim hx.2.1.1],
       have [ident I] [":", expr «expr∀ᶠ in , »((b : set α), v.filter_at x, «expr < »((q : «exprℝ≥0∞»()), «expr / »(ρ b, μ b)))] [":=", expr (tendsto_order.1 L).1 _ hx.2.1.2],
       apply [expr I.frequently.mono (λ a ha, _)],
       rw ["[", expr coe_nnreal_smul_apply, "]"] [],
       exact [expr ennreal.mul_le_of_le_div ha.le]
     end
     «expr = »(..., ρ «expr ∩ »(to_measurable «expr + »(ρ, μ) (u m), to_measurable «expr + »(ρ, μ) (w n))) : begin
       conv_rhs [] [] { rw [expr inter_comm] },
       rw [expr inter_comm] [],
       exact [expr (measure_to_measurable_add_inter_left (measurable_set_to_measurable _ _) J).symm]
     end],
  by_contra [],
  apply [expr lt_irrefl (ρ «expr ∩ »(to_measurable «expr + »(ρ, μ) (u m), to_measurable «expr + »(ρ, μ) (w n)))],
  calc
    «expr ≤ »(ρ «expr ∩ »(to_measurable «expr + »(ρ, μ) (u m), to_measurable «expr + »(ρ, μ) (w n)), «expr * »(p, μ «expr ∩ »(to_measurable «expr + »(ρ, μ) (u m), to_measurable «expr + »(ρ, μ) (w n)))) : A
    «expr < »(..., «expr * »(q, μ «expr ∩ »(to_measurable «expr + »(ρ, μ) (u m), to_measurable «expr + »(ρ, μ) (w n)))) : begin
      apply [expr (ennreal.mul_lt_mul_right h _).2 (ennreal.coe_lt_coe.2 hpq)],
      suffices [ident H] [":", expr «expr ≠ »(«expr + »(ρ, μ) «expr ∩ »(to_measurable «expr + »(ρ, μ) (u m), to_measurable «expr + »(ρ, μ) (w n)), «expr∞»())],
      { simp [] [] ["only"] ["[", expr not_or_distrib, ",", expr ennreal.add_eq_top, ",", expr pi.add_apply, ",", expr ne.def, ",", expr coe_add, "]"] [] ["at", ident H],
        exact [expr H.2] },
      apply [expr (lt_of_le_of_lt (measure_mono (inter_subset_left _ _)) _).ne],
      rw [expr measure_to_measurable] [],
      apply [expr lt_of_le_of_lt (measure_mono _) (measure_spanning_sets_lt_top «expr + »(ρ, μ) m)],
      exact [expr inter_subset_right _ _]
    end
    «expr ≤ »(..., ρ «expr ∩ »(to_measurable «expr + »(ρ, μ) (u m), to_measurable «expr + »(ρ, μ) (w n))) : B
end

theorem ae_measurable_lim_ratio : AeMeasurable (v.lim_ratio ρ) μ :=
  by 
    apply Ennreal.ae_measurable_of_exist_almost_disjoint_supersets _ _ fun p q hpq => _ 
    exact v.exists_measurable_supersets_lim_ratio hρ hpq

/-- A measurable version of `v.lim_ratio ρ`. Do *not* use this definition: it is only a temporary
device to show that `v.lim_ratio` is almost everywhere equal to the Radon-Nikodym derivative. -/
noncomputable def lim_ratio_meas : α → ℝ≥0∞ :=
  (v.ae_measurable_lim_ratio hρ).mk _

theorem lim_ratio_meas_measurable : Measurable (v.lim_ratio_meas hρ) :=
  AeMeasurable.measurable_mk _

theorem ae_tendsto_lim_ratio_meas : ∀ᵐx ∂μ, tendsto (fun a => ρ a / μ a) (v.filter_at x) (𝓝 (v.lim_ratio_meas hρ x)) :=
  by 
    filterUpwards [v.ae_tendsto_lim_ratio hρ, AeMeasurable.ae_eq_mk (v.ae_measurable_lim_ratio hρ)]
    intro x hx h'x 
    rwa [h'x] at hx

-- error in MeasureTheory.Covering.Differentiation: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- If, for all `x` in a set `s`, one has frequently `ρ a / μ a < p`, then `ρ s ≤ p * μ s`, as
proved in `measure_le_of_frequently_le`. Since `ρ a / μ a` tends almost everywhere to
`v.lim_ratio_meas hρ x`, the same property holds for sets `s` on which `v.lim_ratio_meas hρ < p`. -/
theorem measure_le_mul_of_subset_lim_ratio_meas_lt
{p : «exprℝ≥0»()}
{s : set α}
(h : «expr ⊆ »(s, {x | «expr < »(v.lim_ratio_meas hρ x, p)})) : «expr ≤ »(ρ s, «expr * »(p, μ s)) :=
begin
  let [ident t] [] [":=", expr {x : α | tendsto (λ
    a, «expr / »(ρ a, μ a)) (v.filter_at x) (expr𝓝() (v.lim_ratio_meas hρ x))}],
  have [ident A] [":", expr «expr = »(μ «expr ᶜ»(t), 0)] [":=", expr v.ae_tendsto_lim_ratio_meas hρ],
  suffices [ident H] [":", expr «expr ≤ »(ρ «expr ∩ »(s, t), «expr • »(p, μ) «expr ∩ »(s, t))],
  from [expr calc
     «expr = »(ρ s, ρ «expr ∪ »(«expr ∩ »(s, t), «expr ∩ »(s, «expr ᶜ»(t)))) : by rw [expr inter_union_compl] []
     «expr ≤ »(..., «expr + »(ρ «expr ∩ »(s, t), ρ «expr ∩ »(s, «expr ᶜ»(t)))) : measure_union_le _ _
     «expr ≤ »(..., «expr + »(«expr * »(p, μ «expr ∩ »(s, t)), 0)) : add_le_add H ((measure_mono (inter_subset_right _ _)).trans (hρ A).le)
     «expr ≤ »(..., «expr * »(p, μ s)) : by { rw [expr add_zero] [],
       exact [expr ennreal.mul_le_mul le_rfl (measure_mono (inter_subset_left _ _))] }],
  refine [expr v.measure_le_of_frequently_le _ hρ _ (λ x hx, _)],
  have [ident I] [":", expr «expr∀ᶠ in , »((b : set α), v.filter_at x, «expr < »(«expr / »(ρ b, μ b), p))] [":=", expr (tendsto_order.1 hx.2).2 _ (h hx.1)],
  apply [expr I.frequently.mono (λ a ha, _)],
  rw ["[", expr coe_nnreal_smul_apply, "]"] [],
  refine [expr (ennreal.div_le_iff_le_mul _ (or.inr (bot_le.trans_lt ha).ne')).1 ha.le],
  simp [] [] ["only"] ["[", expr ennreal.coe_ne_top, ",", expr ne.def, ",", expr or_true, ",", expr not_false_iff, "]"] [] []
end

-- error in MeasureTheory.Covering.Differentiation: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- If, for all `x` in a set `s`, one has frequently `q < ρ a / μ a`, then `q * μ s ≤ ρ s`, as
proved in `measure_le_of_frequently_le`. Since `ρ a / μ a` tends almost everywhere to
`v.lim_ratio_meas hρ x`, the same property holds for sets `s` on which `q < v.lim_ratio_meas hρ`. -/
theorem mul_measure_le_of_subset_lt_lim_ratio_meas
{q : «exprℝ≥0»()}
{s : set α}
(h : «expr ⊆ »(s, {x | «expr < »((q : «exprℝ≥0∞»()), v.lim_ratio_meas hρ x)})) : «expr ≤ »(«expr * »((q : «exprℝ≥0∞»()), μ s), ρ s) :=
begin
  let [ident t] [] [":=", expr {x : α | tendsto (λ
    a, «expr / »(ρ a, μ a)) (v.filter_at x) (expr𝓝() (v.lim_ratio_meas hρ x))}],
  have [ident A] [":", expr «expr = »(μ «expr ᶜ»(t), 0)] [":=", expr v.ae_tendsto_lim_ratio_meas hρ],
  suffices [ident H] [":", expr «expr ≤ »(«expr • »(q, μ) «expr ∩ »(s, t), ρ «expr ∩ »(s, t))],
  from [expr calc
     «expr = »(«expr • »(q, μ) s, «expr • »(q, μ) «expr ∪ »(«expr ∩ »(s, t), «expr ∩ »(s, «expr ᶜ»(t)))) : by rw [expr inter_union_compl] []
     «expr ≤ »(..., «expr + »(«expr • »(q, μ) «expr ∩ »(s, t), «expr • »(q, μ) «expr ∩ »(s, «expr ᶜ»(t)))) : measure_union_le _ _
     «expr ≤ »(..., «expr + »(ρ «expr ∩ »(s, t), «expr * »(q, μ «expr ᶜ»(t)))) : begin
       apply [expr add_le_add H],
       rw ["[", expr coe_nnreal_smul_apply, "]"] [],
       exact [expr ennreal.mul_le_mul le_rfl (measure_mono (inter_subset_right _ _))]
     end
     «expr ≤ »(..., ρ s) : by { rw ["[", expr A, ",", expr mul_zero, ",", expr add_zero, "]"] [],
       exact [expr measure_mono (inter_subset_left _ _)] }],
  refine [expr v.measure_le_of_frequently_le _ (absolutely_continuous.rfl.coe_nnreal_smul _) _ _],
  assume [binders (x hx)],
  have [ident I] [":", expr «expr∀ᶠ in , »((a), v.filter_at x, «expr < »((q : «exprℝ≥0∞»()), «expr / »(ρ a, μ a)))] [":=", expr (tendsto_order.1 hx.2).1 _ (h hx.1)],
  apply [expr I.frequently.mono (λ a ha, _)],
  rw ["[", expr coe_nnreal_smul_apply, "]"] [],
  exact [expr ennreal.mul_le_of_le_div ha.le]
end

-- error in MeasureTheory.Covering.Differentiation: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- The points with `v.lim_ratio_meas hρ x = ∞` have measure `0` for `μ`. -/
theorem measure_lim_ratio_meas_top : «expr = »(μ {x | «expr = »(v.lim_ratio_meas hρ x, «expr∞»())}, 0) :=
begin
  refine [expr null_of_locally_null _ (λ x hx, _)],
  obtain ["⟨", ident o, ",", ident xo, ",", ident o_open, ",", ident μo, "⟩", ":", expr «expr∃ , »((o : set α), «expr ∧ »(«expr ∈ »(x, o), «expr ∧ »(is_open o, «expr < »(ρ o, «expr∞»())))), ":=", expr measure.exists_is_open_measure_lt_top ρ x],
  refine [expr ⟨o, mem_nhds_within_of_mem_nhds (o_open.mem_nhds xo), le_antisymm _ bot_le⟩],
  let [ident s] [] [":=", expr «expr ∩ »({x : α | «expr = »(v.lim_ratio_meas hρ x, «expr∞»())}, o)],
  have [ident ρs] [":", expr «expr ≠ »(ρ s, «expr∞»())] [":=", expr ((measure_mono (inter_subset_right _ _)).trans_lt μo).ne],
  have [ident A] [":", expr ∀ q : «exprℝ≥0»(), «expr ≤ »(1, q) → «expr ≤ »(μ s, «expr * »(«expr ⁻¹»(q), ρ s))] [],
  { assume [binders (q hq)],
    rw ["[", expr mul_comm, ",", "<-", expr div_eq_mul_inv, ",", expr ennreal.le_div_iff_mul_le _ (or.inr ρs), ",", expr mul_comm, "]"] [],
    { apply [expr v.mul_measure_le_of_subset_lt_lim_ratio_meas hρ],
      assume [binders (y hy)],
      have [] [":", expr «expr = »(v.lim_ratio_meas hρ y, «expr∞»())] [":=", expr hy.1],
      simp [] [] ["only"] ["[", expr this, ",", expr ennreal.coe_lt_top, ",", expr mem_set_of_eq, "]"] [] [] },
    { simp [] [] ["only"] ["[", expr (zero_lt_one.trans_le hq).ne', ",", expr true_or, ",", expr ennreal.coe_eq_zero, ",", expr ne.def, ",", expr not_false_iff, "]"] [] [] } },
  have [ident B] [":", expr tendsto (λ
    q : «exprℝ≥0»(), «expr * »(«expr ⁻¹»((q : «exprℝ≥0∞»())), ρ s)) at_top (expr𝓝() «expr * »(«expr ⁻¹»(«expr∞»()), ρ s))] [],
  { apply [expr ennreal.tendsto.mul_const _ (or.inr ρs)],
    exact [expr ennreal.tendsto_inv_iff.2 (ennreal.tendsto_coe_nhds_top.2 tendsto_id)] },
  simp [] [] ["only"] ["[", expr zero_mul, ",", expr ennreal.inv_top, "]"] [] ["at", ident B],
  apply [expr ge_of_tendsto B],
  exact [expr eventually_at_top.2 ⟨1, A⟩]
end

-- error in MeasureTheory.Covering.Differentiation: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- The points with `v.lim_ratio_meas hρ x = 0` have measure `0` for `ρ`. -/
theorem measure_lim_ratio_meas_zero : «expr = »(ρ {x | «expr = »(v.lim_ratio_meas hρ x, 0)}, 0) :=
begin
  refine [expr null_of_locally_null _ (λ x hx, _)],
  obtain ["⟨", ident o, ",", ident xo, ",", ident o_open, ",", ident μo, "⟩", ":", expr «expr∃ , »((o : set α), «expr ∧ »(«expr ∈ »(x, o), «expr ∧ »(is_open o, «expr < »(μ o, «expr∞»())))), ":=", expr measure.exists_is_open_measure_lt_top μ x],
  refine [expr ⟨o, mem_nhds_within_of_mem_nhds (o_open.mem_nhds xo), le_antisymm _ bot_le⟩],
  let [ident s] [] [":=", expr «expr ∩ »({x : α | «expr = »(v.lim_ratio_meas hρ x, 0)}, o)],
  have [ident μs] [":", expr «expr ≠ »(μ s, «expr∞»())] [":=", expr ((measure_mono (inter_subset_right _ _)).trans_lt μo).ne],
  have [ident A] [":", expr ∀ q : «exprℝ≥0»(), «expr < »(0, q) → «expr ≤ »(ρ s, «expr * »(q, μ s))] [],
  { assume [binders (q hq)],
    apply [expr v.measure_le_mul_of_subset_lim_ratio_meas_lt hρ],
    assume [binders (y hy)],
    have [] [":", expr «expr = »(v.lim_ratio_meas hρ y, 0)] [":=", expr hy.1],
    simp [] [] ["only"] ["[", expr this, ",", expr mem_set_of_eq, ",", expr hq, ",", expr ennreal.coe_pos, "]"] [] [] },
  have [ident B] [":", expr tendsto (λ
    q : «exprℝ≥0»(), «expr * »((q : «exprℝ≥0∞»()), μ s)) «expr𝓝[ ] »(Ioi (0 : «exprℝ≥0»()), 0) (expr𝓝() «expr * »((0 : «exprℝ≥0»()), μ s))] [],
  { apply [expr ennreal.tendsto.mul_const _ (or.inr μs)],
    rw [expr ennreal.tendsto_coe] [],
    exact [expr nhds_within_le_nhds] },
  simp [] [] ["only"] ["[", expr zero_mul, ",", expr ennreal.coe_zero, "]"] [] ["at", ident B],
  apply [expr ge_of_tendsto B],
  filter_upwards ["[", expr self_mem_nhds_within, "]"] [],
  exact [expr A]
end

-- error in MeasureTheory.Covering.Differentiation: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- As an intermediate step to show that `μ.with_density (v.lim_ratio_meas hρ) = ρ`, we show here
that `μ.with_density (v.lim_ratio_meas hρ) ≤ t^2 ρ` for any `t > 1`. -/
theorem with_density_le_mul
{s : set α}
(hs : measurable_set s)
{t : «exprℝ≥0»()}
(ht : «expr < »(1, t)) : «expr ≤ »(μ.with_density (v.lim_ratio_meas hρ) s, «expr * »(«expr ^ »(t, 2), ρ s)) :=
begin
  have [ident t_ne_zero'] [":", expr «expr ≠ »(t, 0)] [":=", expr (zero_lt_one.trans ht).ne'],
  have [ident t_ne_zero] [":", expr «expr ≠ »((t : «exprℝ≥0∞»()), 0)] [],
  by simpa [] [] ["only"] ["[", expr ennreal.coe_eq_zero, ",", expr ne.def, "]"] [] ["using", expr t_ne_zero'],
  let [ident ν] [] [":=", expr μ.with_density (v.lim_ratio_meas hρ)],
  let [ident f] [] [":=", expr v.lim_ratio_meas hρ],
  have [ident f_meas] [":", expr measurable f] [":=", expr v.lim_ratio_meas_measurable hρ],
  have [ident A] [":", expr «expr ≤ »(ν «expr ∩ »(s, «expr ⁻¹' »(f, {0})), «expr • »(«expr ^ »((t : «exprℝ≥0∞»()), 2), ρ) «expr ∩ »(s, «expr ⁻¹' »(f, {0})))] [],
  { apply [expr le_trans _ (zero_le _)],
    have [ident M] [":", expr measurable_set «expr ∩ »(s, «expr ⁻¹' »(f, {0}))] [":=", expr hs.inter (f_meas (measurable_set_singleton _))],
    simp [] [] ["only"] ["[", expr ν, ",", expr f, ",", expr nonpos_iff_eq_zero, ",", expr M, ",", expr with_density_apply, ",", expr lintegral_eq_zero_iff f_meas, "]"] [] [],
    apply [expr (ae_restrict_iff' M).2],
    exact [expr eventually_of_forall (λ x hx, hx.2)] },
  have [ident B] [":", expr «expr ≤ »(ν «expr ∩ »(s, «expr ⁻¹' »(f, {«expr∞»()})), «expr • »(«expr ^ »((t : «exprℝ≥0∞»()), 2), ρ) «expr ∩ »(s, «expr ⁻¹' »(f, {«expr∞»()})))] [],
  { apply [expr le_trans (le_of_eq _) (zero_le _)],
    apply [expr with_density_absolutely_continuous μ _],
    rw ["<-", expr nonpos_iff_eq_zero] [],
    exact [expr (measure_mono (inter_subset_right _ _)).trans (v.measure_lim_ratio_meas_top hρ).le] },
  have [ident C] [":", expr ∀
   n : exprℤ(), «expr ≤ »(ν «expr ∩ »(s, «expr ⁻¹' »(f, Ico «expr ^ »(t, n) «expr ^ »(t, «expr + »(n, 1)))), «expr • »(«expr ^ »((t : «exprℝ≥0∞»()), 2), ρ) «expr ∩ »(s, «expr ⁻¹' »(f, Ico «expr ^ »(t, n) «expr ^ »(t, «expr + »(n, 1)))))] [],
  { assume [binders (n)],
    let [ident I] [] [":=", expr Ico «expr ^ »((t : «exprℝ≥0∞»()), n) «expr ^ »(t, «expr + »(n, 1))],
    have [ident M] [":", expr measurable_set «expr ∩ »(s, «expr ⁻¹' »(f, I))] [":=", expr hs.inter (f_meas measurable_set_Ico)],
    simp [] [] ["only"] ["[", expr f, ",", expr M, ",", expr with_density_apply, ",", expr coe_nnreal_smul_apply, "]"] [] [],
    calc
      «expr ≤ »(«expr∫⁻ in , ∂ »((x), «expr ∩ »(s, «expr ⁻¹' »(f, I)), f x, μ), «expr∫⁻ in , ∂ »((x), «expr ∩ »(s, «expr ⁻¹' »(f, I)), «expr ^ »(t, «expr + »(n, 1)), μ)) : lintegral_mono_ae ((ae_restrict_iff' M).2 (eventually_of_forall (λ
         x hx, hx.2.2.le)))
      «expr = »(..., «expr * »(«expr ^ »(t, «expr + »(n, 1)), μ «expr ∩ »(s, «expr ⁻¹' »(f, I)))) : by simp [] [] ["only"] ["[", expr lintegral_const, ",", expr measurable_set.univ, ",", expr measure.restrict_apply, ",", expr univ_inter, "]"] [] []
      «expr = »(..., «expr * »(«expr ^ »(t, (2 : exprℤ())), «expr * »(«expr ^ »(t, «expr - »(n, 1)), μ «expr ∩ »(s, «expr ⁻¹' »(f, I))))) : begin
        rw ["[", "<-", expr mul_assoc, ",", "<-", expr ennreal.zpow_add t_ne_zero ennreal.coe_ne_top, "]"] [],
        congr' [2] [],
        abel [] [] []
      end
      «expr ≤ »(..., «expr * »(«expr ^ »(t, 2), ρ «expr ∩ »(s, «expr ⁻¹' »(f, I)))) : begin
        apply [expr ennreal.mul_le_mul le_rfl _],
        rw ["<-", expr ennreal.coe_zpow (zero_lt_one.trans ht).ne'] [],
        apply [expr v.mul_measure_le_of_subset_lt_lim_ratio_meas hρ],
        assume [binders (x hx)],
        apply [expr lt_of_lt_of_le _ hx.2.1],
        rw ["[", "<-", expr ennreal.coe_zpow (zero_lt_one.trans ht).ne', ",", expr ennreal.coe_lt_coe, ",", expr sub_eq_add_neg, ",", expr zpow_add₀ t_ne_zero', "]"] [],
        conv_rhs [] [] { rw ["<-", expr mul_one «expr ^ »(t, n)] },
        refine [expr mul_lt_mul' le_rfl _ (zero_le _) (nnreal.zpow_pos t_ne_zero' _)],
        rw [expr zpow_neg_one₀] [],
        exact [expr nnreal.inv_lt_one ht]
      end },
  calc
    «expr = »(ν s, «expr + »(«expr + »(ν «expr ∩ »(s, «expr ⁻¹' »(f, {0})), ν «expr ∩ »(s, «expr ⁻¹' »(f, {«expr∞»()}))), «expr∑' , »((n : exprℤ()), ν «expr ∩ »(s, «expr ⁻¹' »(f, Ico «expr ^ »(t, n) «expr ^ »(t, «expr + »(n, 1))))))) : measure_eq_measure_preimage_add_measure_tsum_Ico_zpow ν f_meas hs ht
    «expr ≤ »(..., «expr + »(«expr + »(«expr • »(«expr ^ »((t : «exprℝ≥0∞»()), 2), ρ) «expr ∩ »(s, «expr ⁻¹' »(f, {0})), «expr • »(«expr ^ »((t : «exprℝ≥0∞»()), 2), ρ) «expr ∩ »(s, «expr ⁻¹' »(f, {«expr∞»()}))), «expr∑' , »((n : exprℤ()), «expr • »(«expr ^ »((t : «exprℝ≥0∞»()), 2), ρ) «expr ∩ »(s, «expr ⁻¹' »(f, Ico «expr ^ »(t, n) «expr ^ »(t, «expr + »(n, 1))))))) : add_le_add (add_le_add A B) (ennreal.tsum_le_tsum C)
    «expr = »(..., «expr • »(«expr ^ »((t : «exprℝ≥0∞»()), 2), ρ) s) : (measure_eq_measure_preimage_add_measure_tsum_Ico_zpow «expr • »(«expr ^ »((t : «exprℝ≥0∞»()), 2), ρ) f_meas hs ht).symm
end

-- error in MeasureTheory.Covering.Differentiation: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- As an intermediate step to show that `μ.with_density (v.lim_ratio_meas hρ) = ρ`, we show here
that `ρ ≤ t μ.with_density (v.lim_ratio_meas hρ)` for any `t > 1`. -/
theorem le_mul_with_density
{s : set α}
(hs : measurable_set s)
{t : «exprℝ≥0»()}
(ht : «expr < »(1, t)) : «expr ≤ »(ρ s, «expr * »(t, μ.with_density (v.lim_ratio_meas hρ) s)) :=
begin
  have [ident t_ne_zero'] [":", expr «expr ≠ »(t, 0)] [":=", expr (zero_lt_one.trans ht).ne'],
  have [ident t_ne_zero] [":", expr «expr ≠ »((t : «exprℝ≥0∞»()), 0)] [],
  by simpa [] [] ["only"] ["[", expr ennreal.coe_eq_zero, ",", expr ne.def, "]"] [] ["using", expr t_ne_zero'],
  let [ident ν] [] [":=", expr μ.with_density (v.lim_ratio_meas hρ)],
  let [ident f] [] [":=", expr v.lim_ratio_meas hρ],
  have [ident f_meas] [":", expr measurable f] [":=", expr v.lim_ratio_meas_measurable hρ],
  have [ident A] [":", expr «expr ≤ »(ρ «expr ∩ »(s, «expr ⁻¹' »(f, {0})), «expr • »(t, ν) «expr ∩ »(s, «expr ⁻¹' »(f, {0})))] [],
  { refine [expr le_trans (measure_mono (inter_subset_right _ _)) (le_trans (le_of_eq _) (zero_le _))],
    exact [expr v.measure_lim_ratio_meas_zero hρ] },
  have [ident B] [":", expr «expr ≤ »(ρ «expr ∩ »(s, «expr ⁻¹' »(f, {«expr∞»()})), «expr • »(t, ν) «expr ∩ »(s, «expr ⁻¹' »(f, {«expr∞»()})))] [],
  { apply [expr le_trans (le_of_eq _) (zero_le _)],
    apply [expr hρ],
    rw ["<-", expr nonpos_iff_eq_zero] [],
    exact [expr (measure_mono (inter_subset_right _ _)).trans (v.measure_lim_ratio_meas_top hρ).le] },
  have [ident C] [":", expr ∀
   n : exprℤ(), «expr ≤ »(ρ «expr ∩ »(s, «expr ⁻¹' »(f, Ico «expr ^ »(t, n) «expr ^ »(t, «expr + »(n, 1)))), «expr • »(t, ν) «expr ∩ »(s, «expr ⁻¹' »(f, Ico «expr ^ »(t, n) «expr ^ »(t, «expr + »(n, 1)))))] [],
  { assume [binders (n)],
    let [ident I] [] [":=", expr Ico «expr ^ »((t : «exprℝ≥0∞»()), n) «expr ^ »(t, «expr + »(n, 1))],
    have [ident M] [":", expr measurable_set «expr ∩ »(s, «expr ⁻¹' »(f, I))] [":=", expr hs.inter (f_meas measurable_set_Ico)],
    simp [] [] ["only"] ["[", expr f, ",", expr M, ",", expr with_density_apply, ",", expr coe_nnreal_smul_apply, "]"] [] [],
    calc
      «expr ≤ »(ρ «expr ∩ »(s, «expr ⁻¹' »(f, I)), «expr * »(«expr ^ »(t, «expr + »(n, 1)), μ «expr ∩ »(s, «expr ⁻¹' »(f, I)))) : begin
        rw ["<-", expr ennreal.coe_zpow t_ne_zero'] [],
        apply [expr v.measure_le_mul_of_subset_lim_ratio_meas_lt hρ],
        assume [binders (x hx)],
        apply [expr hx.2.2.trans_le (le_of_eq _)],
        rw [expr ennreal.coe_zpow t_ne_zero'] []
      end
      «expr = »(..., «expr∫⁻ in , ∂ »((x), «expr ∩ »(s, «expr ⁻¹' »(f, I)), «expr ^ »(t, «expr + »(n, 1)), μ)) : by simp [] [] ["only"] ["[", expr lintegral_const, ",", expr measurable_set.univ, ",", expr measure.restrict_apply, ",", expr univ_inter, "]"] [] []
      «expr ≤ »(..., «expr∫⁻ in , ∂ »((x), «expr ∩ »(s, «expr ⁻¹' »(f, I)), «expr * »(t, f x), μ)) : begin
        apply [expr lintegral_mono_ae ((ae_restrict_iff' M).2 (eventually_of_forall (λ x hx, _)))],
        rw ["[", expr add_comm, ",", expr ennreal.zpow_add t_ne_zero ennreal.coe_ne_top, ",", expr zpow_one, "]"] [],
        exact [expr ennreal.mul_le_mul le_rfl hx.2.1]
      end
      «expr = »(..., «expr * »(t, «expr∫⁻ in , ∂ »((x), «expr ∩ »(s, «expr ⁻¹' »(f, I)), f x, μ))) : lintegral_const_mul _ f_meas },
  calc
    «expr = »(ρ s, «expr + »(«expr + »(ρ «expr ∩ »(s, «expr ⁻¹' »(f, {0})), ρ «expr ∩ »(s, «expr ⁻¹' »(f, {«expr∞»()}))), «expr∑' , »((n : exprℤ()), ρ «expr ∩ »(s, «expr ⁻¹' »(f, Ico «expr ^ »(t, n) «expr ^ »(t, «expr + »(n, 1))))))) : measure_eq_measure_preimage_add_measure_tsum_Ico_zpow ρ f_meas hs ht
    «expr ≤ »(..., «expr + »(«expr + »(«expr • »(t, ν) «expr ∩ »(s, «expr ⁻¹' »(f, {0})), «expr • »(t, ν) «expr ∩ »(s, «expr ⁻¹' »(f, {«expr∞»()}))), «expr∑' , »((n : exprℤ()), «expr • »(t, ν) «expr ∩ »(s, «expr ⁻¹' »(f, Ico «expr ^ »(t, n) «expr ^ »(t, «expr + »(n, 1))))))) : add_le_add (add_le_add A B) (ennreal.tsum_le_tsum C)
    «expr = »(..., «expr • »(t, ν) s) : (measure_eq_measure_preimage_add_measure_tsum_Ico_zpow «expr • »(t, ν) f_meas hs ht).symm
end

-- error in MeasureTheory.Covering.Differentiation: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem with_density_lim_ratio_meas_eq : «expr = »(μ.with_density (v.lim_ratio_meas hρ), ρ) :=
begin
  ext1 [] [ident s, ident hs],
  refine [expr le_antisymm _ _],
  { have [] [":", expr tendsto (λ
      t : «exprℝ≥0»(), («expr * »(«expr ^ »(t, 2), ρ s) : «exprℝ≥0∞»())) «expr𝓝[ ] »(Ioi 1, 1) (expr𝓝() «expr * »(«expr ^ »((1 : «exprℝ≥0»()), 2), ρ s))] [],
    { refine [expr ennreal.tendsto.mul _ _ tendsto_const_nhds _],
      { exact [expr ennreal.tendsto.pow (ennreal.tendsto_coe.2 nhds_within_le_nhds)] },
      { simp [] [] ["only"] ["[", expr one_pow, ",", expr ennreal.coe_one, ",", expr true_or, ",", expr ne.def, ",", expr not_false_iff, ",", expr one_ne_zero, "]"] [] [] },
      { simp [] [] ["only"] ["[", expr one_pow, ",", expr ennreal.coe_one, ",", expr ne.def, ",", expr or_true, ",", expr ennreal.one_ne_top, ",", expr not_false_iff, "]"] [] [] } },
    simp [] [] ["only"] ["[", expr one_pow, ",", expr one_mul, ",", expr ennreal.coe_one, "]"] [] ["at", ident this],
    refine [expr ge_of_tendsto this _],
    filter_upwards ["[", expr self_mem_nhds_within, "]"] [],
    assume [binders (t ht)],
    exact [expr v.with_density_le_mul hρ hs ht] },
  { have [] [":", expr tendsto (λ
      t : «exprℝ≥0»(), «expr * »((t : «exprℝ≥0∞»()), μ.with_density (v.lim_ratio_meas hρ) s)) «expr𝓝[ ] »(Ioi 1, 1) (expr𝓝() «expr * »((1 : «exprℝ≥0»()), μ.with_density (v.lim_ratio_meas hρ) s))] [],
    { refine [expr ennreal.tendsto.mul_const (ennreal.tendsto_coe.2 nhds_within_le_nhds) _],
      simp [] [] ["only"] ["[", expr ennreal.coe_one, ",", expr true_or, ",", expr ne.def, ",", expr not_false_iff, ",", expr one_ne_zero, "]"] [] [] },
    simp [] [] ["only"] ["[", expr one_mul, ",", expr ennreal.coe_one, "]"] [] ["at", ident this],
    refine [expr ge_of_tendsto this _],
    filter_upwards ["[", expr self_mem_nhds_within, "]"] [],
    assume [binders (t ht)],
    exact [expr v.le_mul_with_density hρ hs ht] }
end

-- error in MeasureTheory.Covering.Differentiation: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Weak version of the main theorem on differentiation of measures: given a Vitali family `v`
for a locally finite measure `μ`, and another locally finite measure `ρ`, then for `μ`-almost
every `x` the ratio `ρ a / μ a` converges, when `a` shrinks to `x` along the Vitali family,
towards the Radon-Nikodym derivative of `ρ` with respect to `μ`.

This version assumes that `ρ` is absolutely continuous with respect to `μ`. The general version
without this superfluous assumption is `vitali_family.ae_tendsto_rn_deriv`.
-/
theorem ae_tendsto_rn_deriv_of_absolutely_continuous : «expr∀ᵐ ∂ , »((x), μ, tendsto (λ
  a, «expr / »(ρ a, μ a)) (v.filter_at x) (expr𝓝() (ρ.rn_deriv μ x))) :=
begin
  have [ident A] [":", expr «expr =ᵐ[ ] »((μ.with_density (v.lim_ratio_meas hρ)).rn_deriv μ, μ, v.lim_ratio_meas hρ)] [":=", expr rn_deriv_with_density μ (v.lim_ratio_meas_measurable hρ)],
  rw [expr v.with_density_lim_ratio_meas_eq hρ] ["at", ident A],
  filter_upwards ["[", expr v.ae_tendsto_lim_ratio_meas hρ, ",", expr A, "]"] [],
  assume [binders (x hx h'x)],
  rwa [expr h'x] []
end

end AbsolutelyContinuous

-- error in MeasureTheory.Covering.Differentiation: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Main theorem on differentiation of measures: given a Vitali family `v` for a locally finite
measure `μ`, and another locally finite measure `ρ`, then for `μ`-almost every `x` the
ratio `ρ a / μ a` converges, when `a` shrinks to `x` along the Vitali family, towards the
Radon-Nikodym derivative of `ρ` with respect to `μ`. -/
theorem ae_tendsto_rn_deriv : «expr∀ᵐ ∂ , »((x), μ, tendsto (λ
  a, «expr / »(ρ a, μ a)) (v.filter_at x) (expr𝓝() (ρ.rn_deriv μ x))) :=
begin
  let [ident t] [] [":=", expr μ.with_density (ρ.rn_deriv μ)],
  have [ident eq_add] [":", expr «expr = »(ρ, «expr + »(ρ.singular_part μ, t))] [":=", expr have_lebesgue_decomposition_add _ _],
  have [ident A] [":", expr «expr∀ᵐ ∂ , »((x), μ, tendsto (λ
     a, «expr / »(ρ.singular_part μ a, μ a)) (v.filter_at x) (expr𝓝() 0))] [":=", expr v.ae_eventually_measure_zero_of_singular (mutually_singular_singular_part ρ μ)],
  have [ident B] [":", expr «expr∀ᵐ ∂ , »((x), μ, «expr = »(t.rn_deriv μ x, ρ.rn_deriv μ x))] [":=", expr rn_deriv_with_density μ (measurable_rn_deriv ρ μ)],
  have [ident C] [":", expr «expr∀ᵐ ∂ , »((x), μ, tendsto (λ
     a, «expr / »(t a, μ a)) (v.filter_at x) (expr𝓝() (t.rn_deriv μ x)))] [":=", expr v.ae_tendsto_rn_deriv_of_absolutely_continuous (with_density_absolutely_continuous _ _)],
  filter_upwards ["[", expr A, ",", expr B, ",", expr C, "]"] [],
  assume [binders (x Ax Bx Cx)],
  convert [] [expr Ax.add Cx] [],
  { ext1 [] [ident a],
    conv_lhs [] [] { rw ["[", expr eq_add, "]"] },
    simp [] [] ["only"] ["[", expr pi.add_apply, ",", expr coe_add, ",", expr ennreal.add_div, "]"] [] [] },
  { simp [] [] ["only"] ["[", expr Bx, ",", expr zero_add, "]"] [] [] }
end

end 

end VitaliFamily

