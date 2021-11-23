import Mathbin.Analysis.NormedSpace.Dual 
import Mathbin.MeasureTheory.Function.StronglyMeasurable 
import Mathbin.MeasureTheory.Integral.SetIntegral

/-! # From equality of integrals to equality of functions

This file provides various statements of the general form "if two functions have the same integral
on all sets, then they are equal almost everywhere".
The different lemmas use various hypotheses on the class of functions, on the target space or on the
possible finiteness of the measure.

## Main statements

All results listed below apply to two functions `f, g`, together with two main hypotheses,
* `f` and `g` are integrable on all measurable sets with finite measure,
* for all measurable sets `s` with finite measure, `∫ x in s, f x ∂μ = ∫ x in s, g x ∂μ`.
The conclusion is then `f =ᵐ[μ] g`. The main lemmas are:
* `ae_eq_of_forall_set_integral_eq_of_sigma_finite`: case of a sigma-finite measure.
* `ae_fin_strongly_measurable.ae_eq_of_forall_set_integral_eq`: for functions which are
  `ae_fin_strongly_measurable`.
* `Lp.ae_eq_of_forall_set_integral_eq`: for elements of `Lp`, for `0 < p < ∞`.
* `integrable.ae_eq_of_forall_set_integral_eq`: for integrable functions.

For each of these results, we also provide a lemma about the equality of one function and 0. For
example, `Lp.ae_eq_zero_of_forall_set_integral_eq_zero`.

We also register the corresponding lemma for integrals of `ℝ≥0∞`-valued functions, in
`ae_eq_of_forall_set_lintegral_eq_of_sigma_finite`.

Generally useful lemmas which are not related to integrals:
* `ae_eq_zero_of_forall_inner`: if for all constants `c`, `λ x, inner c (f x) =ᵐ[μ] 0` then
  `f =ᵐ[μ] 0`.
* `ae_eq_zero_of_forall_dual`: if for all constants `c` in the dual space, `λ x, c (f x) =ᵐ[μ] 0`
  then `f =ᵐ[μ] 0`.

-/


open MeasureTheory TopologicalSpace NormedSpace Filter

open_locale Ennreal Nnreal MeasureTheory

namespace MeasureTheory

section AeEqOfForall

variable{α E 𝕜 : Type _}{m : MeasurableSpace α}{μ : Measureₓ α}[IsROrC 𝕜]

-- error in MeasureTheory.Function.AeEqOfIntegral: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem ae_eq_zero_of_forall_inner
[inner_product_space 𝕜 E]
[second_countable_topology E]
{f : α → E}
(hf : ∀ c : E, «expr =ᵐ[ ] »(λ x, (inner c (f x) : 𝕜), μ, 0)) : «expr =ᵐ[ ] »(f, μ, 0) :=
begin
  let [ident s] [] [":=", expr dense_seq E],
  have [ident hs] [":", expr dense_range s] [":=", expr dense_range_dense_seq E],
  have [ident hf'] [":", expr «expr∀ᵐ ∂ , »((x), μ, ∀ n : exprℕ(), «expr = »(inner (s n) (f x), (0 : 𝕜)))] [],
  from [expr ae_all_iff.mpr (λ n, hf (s n))],
  refine [expr hf'.mono (λ x hx, _)],
  rw ["[", expr pi.zero_apply, ",", "<-", expr inner_self_eq_zero, "]"] [],
  have [ident h_closed] [":", expr is_closed {c : E | «expr = »(inner c (f x), (0 : 𝕜))}] [],
  from [expr is_closed_eq (continuous_id.inner continuous_const) continuous_const],
  exact [expr @is_closed_property exprℕ() E _ s (λ c, «expr = »(inner c (f x), (0 : 𝕜))) hs h_closed (λ n, hx n) _]
end

local notation "⟪" x ", " y "⟫" => y x

variable(𝕜)

-- error in MeasureTheory.Function.AeEqOfIntegral: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem ae_eq_zero_of_forall_dual
[normed_group E]
[normed_space 𝕜 E]
[second_countable_topology E]
{f : α → E}
(hf : ∀ c : dual 𝕜 E, «expr =ᵐ[ ] »(λ x, «expr⟪ , ⟫»(f x, c), μ, 0)) : «expr =ᵐ[ ] »(f, μ, 0) :=
begin
  let [ident u] [] [":=", expr dense_seq E],
  have [ident hu] [":", expr dense_range u] [":=", expr dense_range_dense_seq _],
  have [] [":", expr ∀
   n, «expr∃ , »((g : «expr →L[ ] »(E, 𝕜, 𝕜)), «expr ∧ »(«expr ≤ »(«expr∥ ∥»(g), 1), «expr = »(g (u n), norm' 𝕜 (u n))))] [":=", expr λ
   n, exists_dual_vector'' 𝕜 (u n)],
  choose [] [ident s] [ident hs] ["using", expr this],
  have [ident A] [":", expr ∀ a : E, ∀ n, «expr = »(«expr⟪ , ⟫»(a, s n), (0 : 𝕜)) → «expr = »(a, 0)] [],
  { assume [binders (a ha)],
    contrapose ["!"] [ident ha],
    have [ident a_pos] [":", expr «expr < »(0, «expr∥ ∥»(a))] [],
    by simp [] [] ["only"] ["[", expr ha, ",", expr norm_pos_iff, ",", expr ne.def, ",", expr not_false_iff, "]"] [] [],
    have [ident a_mem] [":", expr «expr ∈ »(a, closure (set.range u))] [],
    by simp [] [] [] ["[", expr hu.closure_range, "]"] [] [],
    obtain ["⟨", ident n, ",", ident hn, "⟩", ":", expr «expr∃ , »((n : exprℕ()), «expr < »(dist a (u n), «expr / »(«expr∥ ∥»(a), 2))), ":=", expr metric.mem_closure_range_iff.1 a_mem «expr / »(«expr∥ ∥»(a), 2) (half_pos a_pos)],
    use [expr n],
    have [ident I] [":", expr «expr < »(«expr / »(«expr∥ ∥»(a), 2), «expr∥ ∥»(u n))] [],
    { have [] [":", expr «expr ≤ »(«expr∥ ∥»(a), «expr + »(«expr∥ ∥»(u n), «expr∥ ∥»(«expr - »(a, u n))))] [":=", expr norm_le_insert' _ _],
      have [] [":", expr «expr < »(«expr∥ ∥»(«expr - »(a, u n)), «expr / »(«expr∥ ∥»(a), 2))] [],
      by rwa [expr dist_eq_norm] ["at", ident hn],
      linarith [] [] [] },
    assume [binders (h)],
    apply [expr lt_irrefl «expr∥ ∥»(s n (u n))],
    calc
      «expr = »(«expr∥ ∥»(s n (u n)), «expr∥ ∥»(s n «expr - »(u n, a))) : by simp [] [] ["only"] ["[", expr h, ",", expr sub_zero, ",", expr continuous_linear_map.map_sub, "]"] [] []
      «expr ≤ »(..., «expr * »(1, «expr∥ ∥»(«expr - »(u n, a)))) : continuous_linear_map.le_of_op_norm_le _ (hs n).1 _
      «expr < »(..., «expr / »(«expr∥ ∥»(a), 2)) : by { rw ["[", expr one_mul, "]"] [],
        rwa [expr dist_eq_norm'] ["at", ident hn] }
      «expr < »(..., «expr∥ ∥»(u n)) : I
      «expr = »(..., «expr∥ ∥»(s n (u n))) : by rw ["[", expr (hs n).2, ",", expr norm_norm', "]"] [] },
  have [ident hfs] [":", expr ∀ n : exprℕ(), «expr∀ᵐ ∂ , »((x), μ, «expr = »(«expr⟪ , ⟫»(f x, s n), (0 : 𝕜)))] [],
  from [expr λ n, hf (s n)],
  have [ident hf'] [":", expr «expr∀ᵐ ∂ , »((x), μ, ∀ n : exprℕ(), «expr = »(«expr⟪ , ⟫»(f x, s n), (0 : 𝕜)))] [],
  by rwa [expr ae_all_iff] [],
  exact [expr hf'.mono (λ x hx, A (f x) hx)]
end

variable{𝕜}

end AeEqOfForall

variable{α E :
    Type
      _}{m m0 :
    MeasurableSpace
      α}{μ :
    Measureₓ
      α}{s t :
    Set
      α}[NormedGroup
      E][NormedSpace ℝ E][MeasurableSpace E][BorelSpace E][second_countable_topology E][CompleteSpace E]{p : ℝ≥0∞}

section AeEqOfForallSetIntegralEq

-- error in MeasureTheory.Function.AeEqOfIntegral: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem ae_const_le_iff_forall_lt_measure_zero
{β}
[linear_order β]
[topological_space β]
[order_topology β]
[first_countable_topology β]
(f : α → β)
(c : β) : «expr ↔ »(«expr∀ᵐ ∂ , »((x), μ, «expr ≤ »(c, f x)), ∀
 b «expr < » c, «expr = »(μ {x | «expr ≤ »(f x, b)}, 0)) :=
begin
  rw [expr ae_iff] [],
  push_neg [],
  split,
  { assume [binders (h b hb)],
    exact [expr measure_mono_null (λ y hy, (lt_of_le_of_lt hy hb : _)) h] },
  assume [binders (hc)],
  by_cases [expr h, ":", expr ∀ b, «expr ≤ »(c, b)],
  { have [] [":", expr «expr = »({a : α | «expr < »(f a, c)}, «expr∅»())] [],
    { apply [expr set.eq_empty_iff_forall_not_mem.2 (λ x hx, _)],
      exact [expr (lt_irrefl _ (lt_of_lt_of_le hx (h (f x)))).elim] },
    simp [] [] [] ["[", expr this, "]"] [] [] },
  by_cases [expr H, ":", expr «expr¬ »(is_lub (set.Iio c) c)],
  { have [] [":", expr «expr ∈ »(c, upper_bounds (set.Iio c))] [":=", expr λ y hy, le_of_lt hy],
    obtain ["⟨", ident b, ",", ident b_up, ",", ident bc, "⟩", ":", expr «expr∃ , »((b : β), «expr ∧ »(«expr ∈ »(b, upper_bounds (set.Iio c)), «expr < »(b, c)))],
    by simpa [] [] [] ["[", expr is_lub, ",", expr is_least, ",", expr this, ",", expr lower_bounds, "]"] [] ["using", expr H],
    exact [expr measure_mono_null (λ x hx, b_up hx) (hc b bc)] },
  push_neg ["at", ident H, ident h],
  obtain ["⟨", ident u, ",", ident u_mono, ",", ident u_lt, ",", ident u_lim, ",", "-", "⟩", ":", expr «expr∃ , »((u : exprℕ() → β), «expr ∧ »(strict_mono u, «expr ∧ »(∀
      n : exprℕ(), «expr < »(u n, c), «expr ∧ »(tendsto u at_top (nhds c), ∀
       n : exprℕ(), «expr ∈ »(u n, set.Iio c))))), ":=", expr H.exists_seq_strict_mono_tendsto_of_not_mem (lt_irrefl c) h],
  have [ident h_Union] [":", expr «expr = »({x | «expr < »(f x, c)}, «expr⋃ , »((n : exprℕ()), {x | «expr ≤ »(f x, u n)}))] [],
  { ext1 [] [ident x],
    simp_rw ["[", expr set.mem_Union, ",", expr set.mem_set_of_eq, "]"] [],
    split; intro [ident h],
    { obtain ["⟨", ident n, ",", ident hn, "⟩", ":=", expr ((tendsto_order.1 u_lim).1 _ h).exists],
      exact [expr ⟨n, hn.le⟩] },
    { obtain ["⟨", ident n, ",", ident hn, "⟩", ":=", expr h],
      exact [expr hn.trans_lt (u_lt _)] } },
  rw ["[", expr h_Union, ",", expr measure_Union_null_iff, "]"] [],
  assume [binders (n)],
  exact [expr hc _ (u_lt n)]
end

section Ennreal

open_locale TopologicalSpace

-- error in MeasureTheory.Function.AeEqOfIntegral: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem ae_le_of_forall_set_lintegral_le_of_sigma_finite
[sigma_finite μ]
{f g : α → «exprℝ≥0∞»()}
(hf : measurable f)
(hg : measurable g)
(h : ∀
 s, measurable_set s → «expr < »(μ s, «expr∞»()) → «expr ≤ »(«expr∫⁻ in , ∂ »((x), s, f x, μ), «expr∫⁻ in , ∂ »((x), s, g x, μ))) : «expr ≤ᵐ[ ] »(f, μ, g) :=
begin
  have [ident A] [":", expr ∀
   (ε N : «exprℝ≥0»())
   (p : exprℕ()), «expr < »(0, ε) → «expr = »(μ «expr ∩ »({x | «expr ∧ »(«expr ≤ »(«expr + »(g x, ε), f x), «expr ≤ »(g x, N))}, spanning_sets μ p), 0)] [],
  { assume [binders (ε N p εpos)],
    let [ident s] [] [":=", expr «expr ∩ »({x | «expr ∧ »(«expr ≤ »(«expr + »(g x, ε), f x), «expr ≤ »(g x, N))}, spanning_sets μ p)],
    have [ident s_meas] [":", expr measurable_set s] [],
    { have [ident A] [":", expr measurable_set {x | «expr ≤ »(«expr + »(g x, ε), f x)}] [":=", expr measurable_set_le (hg.add measurable_const) hf],
      have [ident B] [":", expr measurable_set {x | «expr ≤ »(g x, N)}] [":=", expr measurable_set_le hg measurable_const],
      exact [expr (A.inter B).inter (measurable_spanning_sets μ p)] },
    have [ident s_lt_top] [":", expr «expr < »(μ s, «expr∞»())] [":=", expr (measure_mono (set.inter_subset_right _ _)).trans_lt (measure_spanning_sets_lt_top μ p)],
    have [ident A] [":", expr «expr ≤ »(«expr + »(«expr∫⁻ in , ∂ »((x), s, g x, μ), «expr * »(ε, μ s)), «expr + »(«expr∫⁻ in , ∂ »((x), s, g x, μ), 0))] [":=", expr calc
       «expr = »(«expr + »(«expr∫⁻ in , ∂ »((x), s, g x, μ), «expr * »(ε, μ s)), «expr + »(«expr∫⁻ in , ∂ »((x), s, g x, μ), «expr∫⁻ in , ∂ »((x), s, ε, μ))) : by simp [] [] ["only"] ["[", expr lintegral_const, ",", expr set.univ_inter, ",", expr measurable_set.univ, ",", expr measure.restrict_apply, "]"] [] []
       «expr = »(..., «expr∫⁻ in , ∂ »((x), s, «expr + »(g x, ε), μ)) : (lintegral_add hg measurable_const).symm
       «expr ≤ »(..., «expr∫⁻ in , ∂ »((x), s, f x, μ)) : set_lintegral_mono (hg.add measurable_const) hf (λ
        x hx, hx.1.1)
       «expr ≤ »(..., «expr + »(«expr∫⁻ in , ∂ »((x), s, g x, μ), 0)) : by { rw ["[", expr add_zero, "]"] [],
         exact [expr h s s_meas s_lt_top] }],
    have [ident B] [":", expr «expr ≠ »(«expr∫⁻ in , ∂ »((x), s, g x, μ), «expr∞»())] [],
    { apply [expr ne_of_lt],
      calc
        «expr ≤ »(«expr∫⁻ in , ∂ »((x), s, g x, μ), «expr∫⁻ in , ∂ »((x), s, N, μ)) : set_lintegral_mono hg measurable_const (λ
         x hx, hx.1.2)
        «expr = »(..., «expr * »(N, μ s)) : by simp [] [] ["only"] ["[", expr lintegral_const, ",", expr set.univ_inter, ",", expr measurable_set.univ, ",", expr measure.restrict_apply, "]"] [] []
        «expr < »(..., «expr∞»()) : by simp [] [] ["only"] ["[", expr lt_top_iff_ne_top, ",", expr s_lt_top.ne, ",", expr and_false, ",", expr ennreal.coe_ne_top, ",", expr with_top.mul_eq_top_iff, ",", expr ne.def, ",", expr not_false_iff, ",", expr false_and, ",", expr or_self, "]"] [] [] },
    have [] [":", expr «expr ≤ »(«expr * »((ε : «exprℝ≥0∞»()), μ s), 0)] [":=", expr ennreal.le_of_add_le_add_left B A],
    simpa [] [] ["only"] ["[", expr ennreal.coe_eq_zero, ",", expr nonpos_iff_eq_zero, ",", expr mul_eq_zero, ",", expr εpos.ne', ",", expr false_or, "]"] [] [] },
  obtain ["⟨", ident u, ",", ident u_mono, ",", ident u_pos, ",", ident u_lim, "⟩", ":", expr «expr∃ , »((u : exprℕ() → «exprℝ≥0»()), «expr ∧ »(strict_anti u, «expr ∧ »(∀
      n, «expr < »(0, u n), tendsto u at_top (nhds 0)))), ":=", expr exists_seq_strict_anti_tendsto (0 : «exprℝ≥0»())],
  let [ident s] [] [":=", expr λ
   n : exprℕ(), «expr ∩ »({x | «expr ∧ »(«expr ≤ »(«expr + »(g x, u n), f x), «expr ≤ »(g x, (n : «exprℝ≥0»())))}, spanning_sets μ n)],
  have [ident μs] [":", expr ∀ n, «expr = »(μ (s n), 0)] [":=", expr λ n, A _ _ _ (u_pos n)],
  have [ident B] [":", expr «expr ⊆ »(«expr ᶜ»({x | «expr ≤ »(f x, g x)}), «expr⋃ , »((n), s n))] [],
  { assume [binders (x hx)],
    simp [] [] [] [] [] ["at", ident hx],
    have [ident L1] [":", expr «expr∀ᶠ in , »((n), at_top, «expr ≤ »(«expr + »(g x, u n), f x))] [],
    { have [] [":", expr tendsto (λ
        n, «expr + »(g x, u n)) at_top (expr𝓝() «expr + »(g x, (0 : «exprℝ≥0»())))] [":=", expr tendsto_const_nhds.add (ennreal.tendsto_coe.2 u_lim)],
      simp [] [] [] [] [] ["at", ident this],
      exact [expr eventually_le_of_tendsto_lt hx this] },
    have [ident L2] [":", expr «expr∀ᶠ in , »((n : exprℕ()), (at_top : filter exprℕ()), «expr ≤ »(g x, (n : «exprℝ≥0»())))] [],
    { have [] [":", expr tendsto (λ n : exprℕ(), ((n : «exprℝ≥0»()) : «exprℝ≥0∞»())) at_top (expr𝓝() «expr∞»())] [],
      { simp [] [] ["only"] ["[", expr ennreal.coe_nat, "]"] [] [],
        exact [expr ennreal.tendsto_nat_nhds_top] },
      exact [expr eventually_ge_of_tendsto_gt (hx.trans_le le_top) this] },
    apply [expr set.mem_Union.2],
    exact [expr ((L1.and L2).and (eventually_mem_spanning_sets μ x)).exists] },
  refine [expr le_antisymm _ bot_le],
  calc
    «expr ≤ »(μ «expr ᶜ»({x : α | λ x : α, «expr ≤ »(f x, g x) x}), μ «expr⋃ , »((n), s n)) : measure_mono B
    «expr ≤ »(..., «expr∑' , »((n), μ (s n))) : measure_Union_le _
    «expr = »(..., 0) : by simp [] [] ["only"] ["[", expr μs, ",", expr tsum_zero, "]"] [] []
end

-- error in MeasureTheory.Function.AeEqOfIntegral: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem ae_eq_of_forall_set_lintegral_eq_of_sigma_finite
[sigma_finite μ]
{f g : α → «exprℝ≥0∞»()}
(hf : measurable f)
(hg : measurable g)
(h : ∀
 s, measurable_set s → «expr < »(μ s, «expr∞»()) → «expr = »(«expr∫⁻ in , ∂ »((x), s, f x, μ), «expr∫⁻ in , ∂ »((x), s, g x, μ))) : «expr =ᵐ[ ] »(f, μ, g) :=
begin
  have [ident A] [":", expr «expr ≤ᵐ[ ] »(f, μ, g)] [":=", expr ae_le_of_forall_set_lintegral_le_of_sigma_finite hf hg (λ
    s hs h's, le_of_eq (h s hs h's))],
  have [ident B] [":", expr «expr ≤ᵐ[ ] »(g, μ, f)] [":=", expr ae_le_of_forall_set_lintegral_le_of_sigma_finite hg hf (λ
    s hs h's, ge_of_eq (h s hs h's))],
  filter_upwards ["[", expr A, ",", expr B, "]"] [],
  exact [expr λ x, le_antisymm]
end

end Ennreal

section Real

section RealFiniteMeasure

variable[is_finite_measure μ]{f : α → ℝ}

-- error in MeasureTheory.Function.AeEqOfIntegral: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Don't use this lemma. Use `ae_nonneg_of_forall_set_integral_nonneg_of_finite_measure`. -/
theorem ae_nonneg_of_forall_set_integral_nonneg_of_finite_measure_of_measurable
(hfm : measurable f)
(hf : integrable f μ)
(hf_zero : ∀ s, measurable_set s → «expr ≤ »(0, «expr∫ in , ∂ »((x), s, f x, μ))) : «expr ≤ᵐ[ ] »(0, μ, f) :=
begin
  simp_rw ["[", expr eventually_le, ",", expr pi.zero_apply, "]"] [],
  rw [expr ae_const_le_iff_forall_lt_measure_zero] [],
  intros [ident b, ident hb_neg],
  let [ident s] [] [":=", expr {x | «expr ≤ »(f x, b)}],
  have [ident hs] [":", expr measurable_set s] [],
  from [expr measurable_set_le hfm measurable_const],
  have [ident h_int_gt] [":", expr «expr ≤ »(«expr∫ in , ∂ »((x), s, f x, μ), «expr * »(b, (μ s).to_real))] [],
  { have [ident h_const_le] [":", expr «expr ≤ »(«expr∫ in , ∂ »((x), s, f x, μ), «expr∫ in , ∂ »((x), s, b, μ))] [],
    { refine [expr set_integral_mono_ae_restrict hf.integrable_on (integrable_on_const.mpr (or.inr (measure_lt_top μ s))) _],
      rw ["[", expr eventually_le, ",", expr ae_restrict_iff hs, "]"] [],
      exact [expr eventually_of_forall (λ x hxs, hxs)] },
    rwa ["[", expr set_integral_const, ",", expr smul_eq_mul, ",", expr mul_comm, "]"] ["at", ident h_const_le] },
  by_contra [],
  refine [expr (lt_self_iff_false «expr∫ in , ∂ »((x), s, f x, μ)).mp (h_int_gt.trans_lt _)],
  refine [expr (mul_neg_iff.mpr (or.inr ⟨hb_neg, _⟩)).trans_le _],
  swap,
  { simp_rw [expr measure.restrict_restrict hs] [],
    exact [expr hf_zero s hs] },
  refine [expr ennreal.to_real_nonneg.lt_of_ne (λ h_eq, h _)],
  cases [expr (ennreal.to_real_eq_zero_iff _).mp h_eq.symm] ["with", ident hμs_eq_zero, ident hμs_eq_top],
  { exact [expr hμs_eq_zero] },
  { exact [expr absurd hμs_eq_top (measure_lt_top μ s).ne] }
end

-- error in MeasureTheory.Function.AeEqOfIntegral: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem ae_nonneg_of_forall_set_integral_nonneg_of_finite_measure
(hf : integrable f μ)
(hf_zero : ∀ s, measurable_set s → «expr ≤ »(0, «expr∫ in , ∂ »((x), s, f x, μ))) : «expr ≤ᵐ[ ] »(0, μ, f) :=
begin
  rcases [expr hf.1, "with", "⟨", ident f', ",", ident hf'_meas, ",", ident hf_ae, "⟩"],
  have [ident hf'_integrable] [":", expr integrable f' μ] [],
  from [expr integrable.congr hf hf_ae],
  have [ident hf'_zero] [":", expr ∀ s, measurable_set s → «expr ≤ »(0, «expr∫ in , ∂ »((x), s, f' x, μ))] [],
  { intros [ident s, ident hs],
    rw [expr set_integral_congr_ae hs (hf_ae.mono (λ x hx hxs, hx.symm))] [],
    exact [expr hf_zero s hs] },
  exact [expr (ae_nonneg_of_forall_set_integral_nonneg_of_finite_measure_of_measurable hf'_meas hf'_integrable hf'_zero).trans hf_ae.symm.le]
end

end RealFiniteMeasure

-- error in MeasureTheory.Function.AeEqOfIntegral: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem ae_nonneg_restrict_of_forall_set_integral_nonneg_inter
{f : α → exprℝ()}
{t : set α}
(hμt : «expr ≠ »(μ t, «expr∞»()))
(hf : integrable_on f t μ)
(hf_zero : ∀
 s, measurable_set s → «expr ≤ »(0, «expr∫ in , ∂ »((x), «expr ∩ »(s, t), f x, μ))) : «expr ≤ᵐ[ ] »(0, μ.restrict t, f) :=
begin
  haveI [] [":", expr fact «expr < »(μ t, «expr∞»())] [":=", expr ⟨lt_top_iff_ne_top.mpr hμt⟩],
  refine [expr ae_nonneg_of_forall_set_integral_nonneg_of_finite_measure hf (λ s hs, _)],
  simp_rw [expr measure.restrict_restrict hs] [],
  exact [expr hf_zero s hs]
end

theorem ae_nonneg_of_forall_set_integral_nonneg_of_sigma_finite [sigma_finite μ] {f : α → ℝ}
  (hf_int_finite : ∀ s, MeasurableSet s → μ s < ∞ → integrable_on f s μ)
  (hf_zero : ∀ s, MeasurableSet s → μ s < ∞ → 0 ≤ ∫x in s, f x ∂μ) : 0 ≤ᵐ[μ] f :=
  by 
    apply ae_of_forall_measure_lt_top_ae_restrict 
    intro t t_meas t_lt_top 
    apply ae_nonneg_restrict_of_forall_set_integral_nonneg_inter t_lt_top.ne (hf_int_finite t t_meas t_lt_top)
    intro s s_meas 
    exact hf_zero _ (s_meas.inter t_meas) (lt_of_le_of_ltₓ (measure_mono (Set.inter_subset_right _ _)) t_lt_top)

-- error in MeasureTheory.Function.AeEqOfIntegral: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem ae_fin_strongly_measurable.ae_nonneg_of_forall_set_integral_nonneg
{f : α → exprℝ()}
(hf : ae_fin_strongly_measurable f μ)
(hf_int_finite : ∀ s, measurable_set s → «expr < »(μ s, «expr∞»()) → integrable_on f s μ)
(hf_zero : ∀
 s, measurable_set s → «expr < »(μ s, «expr∞»()) → «expr ≤ »(0, «expr∫ in , ∂ »((x), s, f x, μ))) : «expr ≤ᵐ[ ] »(0, μ, f) :=
begin
  let [ident t] [] [":=", expr hf.sigma_finite_set],
  suffices [] [":", expr «expr ≤ᵐ[ ] »(0, μ.restrict t, f)],
  from [expr ae_of_ae_restrict_of_ae_restrict_compl this hf.ae_eq_zero_compl.symm.le],
  haveI [] [":", expr sigma_finite (μ.restrict t)] [":=", expr hf.sigma_finite_restrict],
  refine [expr ae_nonneg_of_forall_set_integral_nonneg_of_sigma_finite (λ s hs hμts, _) (λ s hs hμts, _)],
  { rw ["[", expr integrable_on, ",", expr measure.restrict_restrict hs, "]"] [],
    rw [expr measure.restrict_apply hs] ["at", ident hμts],
    exact [expr hf_int_finite «expr ∩ »(s, t) (hs.inter hf.measurable_set) hμts] },
  { rw [expr measure.restrict_restrict hs] [],
    rw [expr measure.restrict_apply hs] ["at", ident hμts],
    exact [expr hf_zero «expr ∩ »(s, t) (hs.inter hf.measurable_set) hμts] }
end

theorem integrable.ae_nonneg_of_forall_set_integral_nonneg {f : α → ℝ} (hf : integrable f μ)
  (hf_zero : ∀ s, MeasurableSet s → μ s < ∞ → 0 ≤ ∫x in s, f x ∂μ) : 0 ≤ᵐ[μ] f :=
  ae_fin_strongly_measurable.ae_nonneg_of_forall_set_integral_nonneg hf.ae_fin_strongly_measurable
    (fun s hs hμs => hf.integrable_on) hf_zero

theorem ae_nonneg_restrict_of_forall_set_integral_nonneg {f : α → ℝ}
  (hf_int_finite : ∀ s, MeasurableSet s → μ s < ∞ → integrable_on f s μ)
  (hf_zero : ∀ s, MeasurableSet s → μ s < ∞ → 0 ≤ ∫x in s, f x ∂μ) {t : Set α} (ht : MeasurableSet t) (hμt : μ t ≠ ∞) :
  0 ≤ᵐ[μ.restrict t] f :=
  by 
    refine'
      ae_nonneg_restrict_of_forall_set_integral_nonneg_inter hμt (hf_int_finite t ht (lt_top_iff_ne_top.mpr hμt))
        fun s hs => _ 
    refine' hf_zero (s ∩ t) (hs.inter ht) _ 
    exact (measure_mono (Set.inter_subset_right s t)).trans_lt (lt_top_iff_ne_top.mpr hμt)

theorem ae_eq_zero_restrict_of_forall_set_integral_eq_zero_real {f : α → ℝ}
  (hf_int_finite : ∀ s, MeasurableSet s → μ s < ∞ → integrable_on f s μ)
  (hf_zero : ∀ s, MeasurableSet s → μ s < ∞ → (∫x in s, f x ∂μ) = 0) {t : Set α} (ht : MeasurableSet t)
  (hμt : μ t ≠ ∞) : f =ᵐ[μ.restrict t] 0 :=
  by 
    suffices h_and : f ≤ᵐ[μ.restrict t] 0 ∧ 0 ≤ᵐ[μ.restrict t] f 
    exact h_and.1.mp (h_and.2.mono fun x hx1 hx2 => le_antisymmₓ hx2 hx1)
    refine'
      ⟨_,
        ae_nonneg_restrict_of_forall_set_integral_nonneg hf_int_finite (fun s hs hμs => (hf_zero s hs hμs).symm.le) ht
          hμt⟩
    suffices h_neg : 0 ≤ᵐ[μ.restrict t] -f
    ·
      refine' h_neg.mono fun x hx => _ 
      rw [Pi.neg_apply] at hx 
      simpa using hx 
    refine'
      ae_nonneg_restrict_of_forall_set_integral_nonneg (fun s hs hμs => (hf_int_finite s hs hμs).neg)
        (fun s hs hμs => _) ht hμt 
    simpRw [Pi.neg_apply]
    rw [integral_neg, neg_nonneg]
    exact (hf_zero s hs hμs).le

end Real

theorem ae_eq_zero_restrict_of_forall_set_integral_eq_zero {f : α → E}
  (hf_int_finite : ∀ s, MeasurableSet s → μ s < ∞ → integrable_on f s μ)
  (hf_zero : ∀ s : Set α, MeasurableSet s → μ s < ∞ → (∫x in s, f x ∂μ) = 0) {t : Set α} (ht : MeasurableSet t)
  (hμt : μ t ≠ ∞) : f =ᵐ[μ.restrict t] 0 :=
  by 
    refine' ae_eq_zero_of_forall_dual ℝ fun c => _ 
    refine' ae_eq_zero_restrict_of_forall_set_integral_eq_zero_real _ _ ht hμt
    ·
      intro s hs hμs 
      exact ContinuousLinearMap.integrable_comp c (hf_int_finite s hs hμs)
    ·
      intro s hs hμs 
      rw [ContinuousLinearMap.integral_comp_comm c (hf_int_finite s hs hμs), hf_zero s hs hμs]
      exact ContinuousLinearMap.map_zero _

-- error in MeasureTheory.Function.AeEqOfIntegral: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem ae_eq_restrict_of_forall_set_integral_eq
{f g : α → E}
(hf_int_finite : ∀ s, measurable_set s → «expr < »(μ s, «expr∞»()) → integrable_on f s μ)
(hg_int_finite : ∀ s, measurable_set s → «expr < »(μ s, «expr∞»()) → integrable_on g s μ)
(hfg_zero : ∀
 s : set α, measurable_set s → «expr < »(μ s, «expr∞»()) → «expr = »(«expr∫ in , ∂ »((x), s, f x, μ), «expr∫ in , ∂ »((x), s, g x, μ)))
{t : set α}
(ht : measurable_set t)
(hμt : «expr ≠ »(μ t, «expr∞»())) : «expr =ᵐ[ ] »(f, μ.restrict t, g) :=
begin
  rw ["<-", expr sub_ae_eq_zero] [],
  have [ident hfg'] [":", expr ∀
   s : set α, measurable_set s → «expr < »(μ s, «expr∞»()) → «expr = »(«expr∫ in , ∂ »((x), s, «expr - »(f, g) x, μ), 0)] [],
  { intros [ident s, ident hs, ident hμs],
    rw [expr integral_sub' (hf_int_finite s hs hμs) (hg_int_finite s hs hμs)] [],
    exact [expr sub_eq_zero.mpr (hfg_zero s hs hμs)] },
  have [ident hfg_int] [":", expr ∀
   s, measurable_set s → «expr < »(μ s, «expr∞»()) → integrable_on «expr - »(f, g) s μ] [],
  from [expr λ s hs hμs, (hf_int_finite s hs hμs).sub (hg_int_finite s hs hμs)],
  exact [expr ae_eq_zero_restrict_of_forall_set_integral_eq_zero hfg_int hfg' ht hμt]
end

-- error in MeasureTheory.Function.AeEqOfIntegral: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem ae_eq_zero_of_forall_set_integral_eq_of_sigma_finite
[sigma_finite μ]
{f : α → E}
(hf_int_finite : ∀ s, measurable_set s → «expr < »(μ s, «expr∞»()) → integrable_on f s μ)
(hf_zero : ∀
 s : set α, measurable_set s → «expr < »(μ s, «expr∞»()) → «expr = »(«expr∫ in , ∂ »((x), s, f x, μ), 0)) : «expr =ᵐ[ ] »(f, μ, 0) :=
begin
  let [ident S] [] [":=", expr spanning_sets μ],
  rw ["[", "<-", expr @measure.restrict_univ _ _ μ, ",", "<-", expr Union_spanning_sets μ, ",", expr eventually_eq, ",", expr ae_iff, ",", expr measure.restrict_apply' (measurable_set.Union (measurable_spanning_sets μ)), "]"] [],
  rw ["[", expr set.inter_Union, ",", expr measure_Union_null_iff, "]"] [],
  intro [ident n],
  have [ident h_meas_n] [":", expr measurable_set (S n)] [],
  from [expr measurable_spanning_sets μ n],
  have [ident hμn] [":", expr «expr < »(μ (S n), «expr∞»())] [],
  from [expr measure_spanning_sets_lt_top μ n],
  rw ["<-", expr measure.restrict_apply' h_meas_n] [],
  exact [expr ae_eq_zero_restrict_of_forall_set_integral_eq_zero hf_int_finite hf_zero h_meas_n hμn.ne]
end

-- error in MeasureTheory.Function.AeEqOfIntegral: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem ae_eq_of_forall_set_integral_eq_of_sigma_finite
[sigma_finite μ]
{f g : α → E}
(hf_int_finite : ∀ s, measurable_set s → «expr < »(μ s, «expr∞»()) → integrable_on f s μ)
(hg_int_finite : ∀ s, measurable_set s → «expr < »(μ s, «expr∞»()) → integrable_on g s μ)
(hfg_eq : ∀
 s : set α, measurable_set s → «expr < »(μ s, «expr∞»()) → «expr = »(«expr∫ in , ∂ »((x), s, f x, μ), «expr∫ in , ∂ »((x), s, g x, μ))) : «expr =ᵐ[ ] »(f, μ, g) :=
begin
  rw ["<-", expr sub_ae_eq_zero] [],
  have [ident hfg] [":", expr ∀
   s : set α, measurable_set s → «expr < »(μ s, «expr∞»()) → «expr = »(«expr∫ in , ∂ »((x), s, «expr - »(f, g) x, μ), 0)] [],
  { intros [ident s, ident hs, ident hμs],
    rw ["[", expr integral_sub' (hf_int_finite s hs hμs) (hg_int_finite s hs hμs), ",", expr sub_eq_zero.mpr (hfg_eq s hs hμs), "]"] [] },
  have [ident hfg_int] [":", expr ∀
   s, measurable_set s → «expr < »(μ s, «expr∞»()) → integrable_on «expr - »(f, g) s μ] [],
  from [expr λ s hs hμs, (hf_int_finite s hs hμs).sub (hg_int_finite s hs hμs)],
  exact [expr ae_eq_zero_of_forall_set_integral_eq_of_sigma_finite hfg_int hfg]
end

-- error in MeasureTheory.Function.AeEqOfIntegral: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem ae_fin_strongly_measurable.ae_eq_zero_of_forall_set_integral_eq_zero
{f : α → E}
(hf_int_finite : ∀ s, measurable_set s → «expr < »(μ s, «expr∞»()) → integrable_on f s μ)
(hf_zero : ∀ s : set α, measurable_set s → «expr < »(μ s, «expr∞»()) → «expr = »(«expr∫ in , ∂ »((x), s, f x, μ), 0))
(hf : ae_fin_strongly_measurable f μ) : «expr =ᵐ[ ] »(f, μ, 0) :=
begin
  let [ident t] [] [":=", expr hf.sigma_finite_set],
  suffices [] [":", expr «expr =ᵐ[ ] »(f, μ.restrict t, 0)],
  from [expr ae_of_ae_restrict_of_ae_restrict_compl this hf.ae_eq_zero_compl],
  haveI [] [":", expr sigma_finite (μ.restrict t)] [":=", expr hf.sigma_finite_restrict],
  refine [expr ae_eq_zero_of_forall_set_integral_eq_of_sigma_finite _ _],
  { intros [ident s, ident hs, ident hμs],
    rw ["[", expr integrable_on, ",", expr measure.restrict_restrict hs, "]"] [],
    rw ["[", expr measure.restrict_apply hs, "]"] ["at", ident hμs],
    exact [expr hf_int_finite _ (hs.inter hf.measurable_set) hμs] },
  { intros [ident s, ident hs, ident hμs],
    rw ["[", expr measure.restrict_restrict hs, "]"] [],
    rw ["[", expr measure.restrict_apply hs, "]"] ["at", ident hμs],
    exact [expr hf_zero _ (hs.inter hf.measurable_set) hμs] }
end

-- error in MeasureTheory.Function.AeEqOfIntegral: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem ae_fin_strongly_measurable.ae_eq_of_forall_set_integral_eq
{f g : α → E}
(hf_int_finite : ∀ s, measurable_set s → «expr < »(μ s, «expr∞»()) → integrable_on f s μ)
(hg_int_finite : ∀ s, measurable_set s → «expr < »(μ s, «expr∞»()) → integrable_on g s μ)
(hfg_eq : ∀
 s : set α, measurable_set s → «expr < »(μ s, «expr∞»()) → «expr = »(«expr∫ in , ∂ »((x), s, f x, μ), «expr∫ in , ∂ »((x), s, g x, μ)))
(hf : ae_fin_strongly_measurable f μ)
(hg : ae_fin_strongly_measurable g μ) : «expr =ᵐ[ ] »(f, μ, g) :=
begin
  rw ["<-", expr sub_ae_eq_zero] [],
  have [ident hfg] [":", expr ∀
   s : set α, measurable_set s → «expr < »(μ s, «expr∞»()) → «expr = »(«expr∫ in , ∂ »((x), s, «expr - »(f, g) x, μ), 0)] [],
  { intros [ident s, ident hs, ident hμs],
    rw ["[", expr integral_sub' (hf_int_finite s hs hμs) (hg_int_finite s hs hμs), ",", expr sub_eq_zero.mpr (hfg_eq s hs hμs), "]"] [] },
  have [ident hfg_int] [":", expr ∀
   s, measurable_set s → «expr < »(μ s, «expr∞»()) → integrable_on «expr - »(f, g) s μ] [],
  from [expr λ s hs hμs, (hf_int_finite s hs hμs).sub (hg_int_finite s hs hμs)],
  exact [expr (hf.sub hg).ae_eq_zero_of_forall_set_integral_eq_zero hfg_int hfg]
end

theorem Lp.ae_eq_zero_of_forall_set_integral_eq_zero (f : Lp E p μ) (hp_ne_zero : p ≠ 0) (hp_ne_top : p ≠ ∞)
  (hf_int_finite : ∀ s, MeasurableSet s → μ s < ∞ → integrable_on f s μ)
  (hf_zero : ∀ s : Set α, MeasurableSet s → μ s < ∞ → (∫x in s, f x ∂μ) = 0) : f =ᵐ[μ] 0 :=
  ae_fin_strongly_measurable.ae_eq_zero_of_forall_set_integral_eq_zero hf_int_finite hf_zero
    (Lp.fin_strongly_measurable _ hp_ne_zero hp_ne_top).AeFinStronglyMeasurable

theorem Lp.ae_eq_of_forall_set_integral_eq (f g : Lp E p μ) (hp_ne_zero : p ≠ 0) (hp_ne_top : p ≠ ∞)
  (hf_int_finite : ∀ s, MeasurableSet s → μ s < ∞ → integrable_on f s μ)
  (hg_int_finite : ∀ s, MeasurableSet s → μ s < ∞ → integrable_on g s μ)
  (hfg : ∀ s : Set α, MeasurableSet s → μ s < ∞ → (∫x in s, f x ∂μ) = ∫x in s, g x ∂μ) : f =ᵐ[μ] g :=
  ae_fin_strongly_measurable.ae_eq_of_forall_set_integral_eq hf_int_finite hg_int_finite hfg
    (Lp.fin_strongly_measurable _ hp_ne_zero hp_ne_top).AeFinStronglyMeasurable
    (Lp.fin_strongly_measurable _ hp_ne_zero hp_ne_top).AeFinStronglyMeasurable

-- error in MeasureTheory.Function.AeEqOfIntegral: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem ae_eq_zero_of_forall_set_integral_eq_of_fin_strongly_measurable_trim
(hm : «expr ≤ »(m, m0))
{f : α → E}
(hf_int_finite : ∀ s, «exprmeasurable_set[ ]»(m) s → «expr < »(μ s, «expr∞»()) → integrable_on f s μ)
(hf_zero : ∀
 s : set α, «exprmeasurable_set[ ]»(m) s → «expr < »(μ s, «expr∞»()) → «expr = »(«expr∫ in , ∂ »((x), s, f x, μ), 0))
(hf : fin_strongly_measurable f (μ.trim hm)) : «expr =ᵐ[ ] »(f, μ, 0) :=
begin
  obtain ["⟨", ident t, ",", ident ht_meas, ",", ident htf_zero, ",", ident htμ, "⟩", ":=", expr hf.exists_set_sigma_finite],
  haveI [] [":", expr sigma_finite ((μ.restrict t).trim hm)] [":=", expr by rwa [expr restrict_trim hm μ ht_meas] ["at", ident htμ]],
  have [ident htf_zero] [":", expr «expr =ᵐ[ ] »(f, μ.restrict «expr ᶜ»(t), 0)] [],
  { rw ["[", expr eventually_eq, ",", expr ae_restrict_iff' (measurable_set.compl (hm _ ht_meas)), "]"] [],
    exact [expr eventually_of_forall htf_zero] },
  have [ident hf_meas_m] [":", expr @measurable _ _ m _ f] [],
  from [expr hf.measurable],
  suffices [] [":", expr «expr =ᵐ[ ] »(f, μ.restrict t, 0)],
  from [expr ae_of_ae_restrict_of_ae_restrict_compl this htf_zero],
  refine [expr measure_eq_zero_of_trim_eq_zero hm _],
  refine [expr ae_eq_zero_of_forall_set_integral_eq_of_sigma_finite _ _],
  { intros [ident s, ident hs, ident hμs],
    rw ["[", expr integrable_on, ",", expr restrict_trim hm (μ.restrict t) hs, ",", expr measure.restrict_restrict (hm s hs), "]"] [],
    rw ["[", "<-", expr restrict_trim hm μ ht_meas, ",", expr measure.restrict_apply hs, ",", expr trim_measurable_set_eq hm (@measurable_set.inter _ m _ _ hs ht_meas), "]"] ["at", ident hμs],
    refine [expr integrable.trim hm _ hf_meas_m],
    exact [expr hf_int_finite _ (@measurable_set.inter _ m _ _ hs ht_meas) hμs] },
  { intros [ident s, ident hs, ident hμs],
    rw ["[", expr restrict_trim hm (μ.restrict t) hs, ",", expr measure.restrict_restrict (hm s hs), "]"] [],
    rw ["[", "<-", expr restrict_trim hm μ ht_meas, ",", expr measure.restrict_apply hs, ",", expr trim_measurable_set_eq hm (@measurable_set.inter _ m _ _ hs ht_meas), "]"] ["at", ident hμs],
    rw ["<-", expr integral_trim hm hf_meas_m] [],
    exact [expr hf_zero _ (@measurable_set.inter _ m _ _ hs ht_meas) hμs] }
end

-- error in MeasureTheory.Function.AeEqOfIntegral: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem integrable.ae_eq_zero_of_forall_set_integral_eq_zero
{f : α → E}
(hf : integrable f μ)
(hf_zero : ∀
 s, measurable_set s → «expr < »(μ s, «expr∞»()) → «expr = »(«expr∫ in , ∂ »((x), s, f x, μ), 0)) : «expr =ᵐ[ ] »(f, μ, 0) :=
begin
  have [ident hf_Lp] [":", expr mem_ℒp f 1 μ] [],
  from [expr mem_ℒp_one_iff_integrable.mpr hf],
  let [ident f_Lp] [] [":=", expr hf_Lp.to_Lp f],
  have [ident hf_f_Lp] [":", expr «expr =ᵐ[ ] »(f, μ, f_Lp)] [],
  from [expr (mem_ℒp.coe_fn_to_Lp hf_Lp).symm],
  refine [expr hf_f_Lp.trans _],
  refine [expr Lp.ae_eq_zero_of_forall_set_integral_eq_zero f_Lp one_ne_zero ennreal.coe_ne_top _ _],
  { exact [expr λ s hs hμs, integrable.integrable_on (L1.integrable_coe_fn _)] },
  { intros [ident s, ident hs, ident hμs],
    rw [expr integral_congr_ae (ae_restrict_of_ae hf_f_Lp.symm)] [],
    exact [expr hf_zero s hs hμs] }
end

-- error in MeasureTheory.Function.AeEqOfIntegral: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem integrable.ae_eq_of_forall_set_integral_eq
(f g : α → E)
(hf : integrable f μ)
(hg : integrable g μ)
(hfg : ∀
 s : set α, measurable_set s → «expr < »(μ s, «expr∞»()) → «expr = »(«expr∫ in , ∂ »((x), s, f x, μ), «expr∫ in , ∂ »((x), s, g x, μ))) : «expr =ᵐ[ ] »(f, μ, g) :=
begin
  rw ["<-", expr sub_ae_eq_zero] [],
  have [ident hfg'] [":", expr ∀
   s : set α, measurable_set s → «expr < »(μ s, «expr∞»()) → «expr = »(«expr∫ in , ∂ »((x), s, «expr - »(f, g) x, μ), 0)] [],
  { intros [ident s, ident hs, ident hμs],
    rw [expr integral_sub' hf.integrable_on hg.integrable_on] [],
    exact [expr sub_eq_zero.mpr (hfg s hs hμs)] },
  exact [expr integrable.ae_eq_zero_of_forall_set_integral_eq_zero (hf.sub hg) hfg']
end

end AeEqOfForallSetIntegralEq

section Lintegral

theorem ae_measurable.ae_eq_of_forall_set_lintegral_eq {f g : α → ℝ≥0∞} (hf : AeMeasurable f μ) (hg : AeMeasurable g μ)
  (hfi : (∫⁻x, f x ∂μ) ≠ ∞) (hgi : (∫⁻x, g x ∂μ) ≠ ∞)
  (hfg : ∀ ⦃s⦄, MeasurableSet s → μ s < ∞ → (∫⁻x in s, f x ∂μ) = ∫⁻x in s, g x ∂μ) : f =ᵐ[μ] g :=
  by 
    refine'
      Ennreal.eventually_eq_of_to_real_eventually_eq (ae_lt_top' hf hfi).ne_of_lt (ae_lt_top' hg hgi).ne_of_lt
        (integrable.ae_eq_of_forall_set_integral_eq _ _ (integrable_to_real_of_lintegral_ne_top hf hfi)
          (integrable_to_real_of_lintegral_ne_top hg hgi) fun s hs hs' => _)
    rw [integral_eq_lintegral_of_nonneg_ae, integral_eq_lintegral_of_nonneg_ae]
    ·
      congr 1
      rw [lintegral_congr_ae (of_real_to_real_ae_eq _), lintegral_congr_ae (of_real_to_real_ae_eq _)]
      ·
        exact hfg hs hs'
      ·
        refine' ae_lt_top' hg.restrict (ne_of_ltₓ (lt_of_le_of_ltₓ _ hgi.lt_top))
        exact @set_lintegral_univ α _ μ g ▸ lintegral_mono_set (Set.subset_univ _)
      ·
        refine' ae_lt_top' hf.restrict (ne_of_ltₓ (lt_of_le_of_ltₓ _ hfi.lt_top))
        exact @set_lintegral_univ α _ μ f ▸ lintegral_mono_set (Set.subset_univ _)
    exacts[ae_of_all _ fun x => Ennreal.to_real_nonneg, hg.ennreal_to_real.restrict,
      ae_of_all _ fun x => Ennreal.to_real_nonneg, hf.ennreal_to_real.restrict]

end Lintegral

end MeasureTheory

