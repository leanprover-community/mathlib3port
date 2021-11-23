import Mathbin.MeasureTheory.Measure.Regular 
import Mathbin.MeasureTheory.Function.SimpleFuncDense 
import Mathbin.Topology.UrysohnsLemma

/-!
# Approximation in Lᵖ by continuous functions

This file proves that bounded continuous functions are dense in `Lp E p μ`, for `1 ≤ p < ∞`, if the
domain `α` of the functions is a normal topological space and the measure `μ` is weakly regular.

The result is presented in several versions:
* `measure_theory.Lp.bounded_continuous_function_dense`: The subgroup
  `measure_theory.Lp.bounded_continuous_function` of `Lp E p μ`, the additive subgroup of
  `Lp E p μ` consisting of equivalence classes containing a continuous representative, is dense in
  `Lp E p μ`.
* `bounded_continuous_function.to_Lp_dense_range`: For finite-measure `μ`, the continuous linear
  map `bounded_continuous_function.to_Lp p μ 𝕜` from `α →ᵇ E` to `Lp E p μ` has dense range.
* `continuous_map.to_Lp_dense_range`: For compact `α` and finite-measure `μ`, the continuous linear
  map `continuous_map.to_Lp p μ 𝕜` from `C(α, E)` to `Lp E p μ` has dense range.

Note that for `p = ∞` this result is not true:  the characteristic function of the set `[0, ∞)` in
`ℝ` cannot be continuously approximated in `L∞`.

The proof is in three steps.  First, since simple functions are dense in `Lp`, it suffices to prove
the result for a scalar multiple of a characteristic function of a measurable set `s`. Secondly,
since the measure `μ` is weakly regular, the set `s` can be approximated above by an open set and
below by a closed set.  Finally, since the domain `α` is normal, we use Urysohn's lemma to find a
continuous function interpolating between these two sets.

## Related results

Are you looking for a result on "directional" approximation (above or below with respect to an
order) of functions whose codomain is `ℝ≥0∞` or `ℝ`, by semicontinuous functions?  See the
Vitali-Carathéodory theorem, in the file `measure_theory.vitali_caratheodory`.

-/


open_locale Ennreal Nnreal TopologicalSpace BoundedContinuousFunction

open MeasureTheory TopologicalSpace ContinuousMap

variable{α : Type _}[MeasurableSpace α][TopologicalSpace α][NormalSpace α][BorelSpace α]

variable(E : Type _)[MeasurableSpace E][NormedGroup E][BorelSpace E][second_countable_topology E]

variable{p : ℝ≥0∞}[_i : Fact (1 ≤ p)](hp : p ≠ ∞)(μ : Measureₓ α)

include _i hp

namespace MeasureTheory.lp

variable[NormedSpace ℝ E]

-- error in MeasureTheory.Function.ContinuousMapDense: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- A function in `Lp` can be approximated in `Lp` by continuous functions. -/
theorem bounded_continuous_function_dense
[μ.weakly_regular] : «expr = »((bounded_continuous_function E p μ).topological_closure, «expr⊤»()) :=
begin
  have [ident hp₀] [":", expr «expr < »(0, p)] [":=", expr lt_of_lt_of_le ennreal.zero_lt_one _i.elim],
  have [ident hp₀'] [":", expr «expr ≤ »(0, «expr / »(1, p.to_real))] [":=", expr div_nonneg zero_le_one ennreal.to_real_nonneg],
  have [ident hp₀''] [":", expr «expr < »(0, p.to_real)] [],
  { simpa [] [] [] ["[", "<-", expr ennreal.to_real_lt_to_real ennreal.zero_ne_top hp, "]"] [] ["using", expr hp₀] },
  suffices [] [":", expr ∀
   (c : E)
   {s : set α}
   (hs : measurable_set s)
   (hμs : «expr < »(μ s, «expr⊤»())), «expr ∈ »((Lp.simple_func.indicator_const p hs hμs.ne c : Lp E p μ), (bounded_continuous_function E p μ).topological_closure)],
  { rw [expr add_subgroup.eq_top_iff'] [],
    refine [expr Lp.induction hp _ _ _ _],
    { exact [expr this] },
    { exact [expr λ f g hf hg hfg', add_subgroup.add_mem _] },
    { exact [expr add_subgroup.is_closed_topological_closure _] } },
  intros [ident c, ident s, ident hs, ident hsμ],
  refine [expr mem_closure_iff_frequently.mpr _],
  rw [expr metric.nhds_basis_closed_ball.frequently_iff] [],
  intros [ident ε, ident hε],
  obtain ["⟨", ident η, ",", ident hη_pos, ",", ident hη_le, "⟩", ":", expr «expr∃ , »((η), «expr ∧ »(«expr < »(0, η), «expr ≤ »((«expr↑ »(«expr * »(«expr∥ ∥₊»(bit0 «expr∥ ∥»(c)), «expr ^ »(«expr * »(2, η), «expr / »(1, p.to_real)))) : exprℝ()), ε)))],
  { have [] [":", expr filter.tendsto (λ
      x : «exprℝ≥0»(), «expr * »(«expr∥ ∥₊»(bit0 «expr∥ ∥»(c)), «expr ^ »(«expr * »(2, x), «expr / »(1, p.to_real)))) (expr𝓝() 0) (expr𝓝() 0)] [],
    { have [] [":", expr filter.tendsto (λ
        x : «exprℝ≥0»(), «expr * »(2, x)) (expr𝓝() 0) (expr𝓝() «expr * »(2, 0))] [":=", expr filter.tendsto_id.const_mul 2],
      convert [] [expr ((nnreal.continuous_at_rpow_const (or.inr hp₀')).tendsto.comp this).const_mul _] [],
      simp [] [] [] ["[", expr hp₀''.ne', "]"] [] [] },
    let [ident ε'] [":", expr «exprℝ≥0»()] [":=", expr ⟨ε, hε.le⟩],
    have [ident hε'] [":", expr «expr < »(0, ε')] [":=", expr by exact_mod_cast [expr hε]],
    obtain ["⟨", ident δ, ",", ident hδ, ",", ident hδε', "⟩", ":=", expr nnreal.nhds_zero_basis.eventually_iff.mp (eventually_le_of_tendsto_lt hε' this)],
    obtain ["⟨", ident η, ",", ident hη, ",", ident hηδ, "⟩", ":=", expr exists_between hδ],
    refine [expr ⟨η, hη, _⟩],
    exact_mod_cast [expr hδε' hηδ] },
  have [ident hη_pos'] [":", expr «expr < »((0 : «exprℝ≥0∞»()), η)] [":=", expr ennreal.coe_pos.2 hη_pos],
  obtain ["⟨", ident u, ",", ident su, ",", ident u_open, ",", ident μu, "⟩", ":", expr «expr∃ , »((u «expr ⊇ » s), «expr ∧ »(is_open u, «expr < »(μ u, «expr + »(μ s, «expr↑ »(η)))))],
  { refine [expr s.exists_is_open_lt_of_lt _ _],
    simpa [] [] [] [] [] ["using", expr ennreal.add_lt_add_left hsμ.ne hη_pos'] },
  obtain ["⟨", ident F, ",", ident Fs, ",", ident F_closed, ",", ident μF, "⟩", ":", expr «expr∃ , »((F «expr ⊆ » s), «expr ∧ »(is_closed F, «expr < »(μ s, «expr + »(μ F, «expr↑ »(η))))), ":=", expr hs.exists_is_closed_lt_add hsμ.ne hη_pos'.ne'],
  have [] [":", expr disjoint «expr ᶜ»(u) F] [],
  { rw ["[", expr set.disjoint_iff_inter_eq_empty, ",", expr set.inter_comm, ",", "<-", expr set.subset_compl_iff_disjoint, "]"] [],
    simpa [] [] [] [] [] ["using", expr Fs.trans su] },
  have [ident h_μ_sdiff] [":", expr «expr ≤ »(μ «expr \ »(u, F), «expr * »(2, η))] [],
  { have [ident hFμ] [":", expr «expr < »(μ F, «expr⊤»())] [":=", expr (measure_mono Fs).trans_lt hsμ],
    refine [expr ennreal.le_of_add_le_add_left hFμ.ne _],
    have [] [":", expr «expr < »(μ u, «expr + »(«expr + »(μ F, «expr↑ »(η)), «expr↑ »(η)))] [],
    from [expr μu.trans (ennreal.add_lt_add_right ennreal.coe_ne_top μF)],
    convert [] [expr this.le] ["using", 1],
    { rw ["[", expr add_comm, ",", "<-", expr measure_union, ",", expr set.diff_union_of_subset (Fs.trans su), "]"] [],
      { exact [expr disjoint_sdiff_self_left] },
      { exact [expr (u_open.sdiff F_closed).measurable_set] },
      { exact [expr F_closed.measurable_set] } },
    have [] [":", expr «expr = »(«expr * »((2 : «exprℝ≥0∞»()), η), «expr + »(η, η))] [":=", expr by simpa [] [] [] [] [] ["using", expr add_mul (1 : «exprℝ≥0∞»()) 1 η]],
    rw [expr this] [],
    abel [] [] [] },
  obtain ["⟨", ident g, ",", ident hgu, ",", ident hgF, ",", ident hg_range, "⟩", ":=", expr exists_continuous_zero_one_of_closed u_open.is_closed_compl F_closed this],
  have [ident g_norm] [":", expr ∀
   x, «expr = »(«expr∥ ∥»(g x), g x)] [":=", expr λ
   x, by rw ["[", expr real.norm_eq_abs, ",", expr abs_of_nonneg (hg_range x).1, "]"] []],
  have [ident gc_bd] [":", expr ∀
   x, «expr ≤ »(«expr∥ ∥»(«expr - »(«expr • »(g x, c), s.indicator (λ
       x, c) x)), «expr∥ ∥»(«expr \ »(u, F).indicator (λ x, bit0 «expr∥ ∥»(c)) x))] [],
  { intros [ident x],
    by_cases [expr hu, ":", expr «expr ∈ »(x, u)],
    { rw ["<-", expr set.diff_union_of_subset (Fs.trans su)] ["at", ident hu],
      cases [expr hu] ["with", ident hFu, ident hF],
      { refine [expr (norm_sub_le _ _).trans _],
        refine [expr (add_le_add_left (norm_indicator_le_norm_self (λ x, c) x) _).trans _],
        have [ident h₀] [":", expr «expr ≤ »(«expr + »(«expr * »(g x, «expr∥ ∥»(c)), «expr∥ ∥»(c)), «expr * »(2, «expr∥ ∥»(c)))] [],
        { nlinarith [] [] ["[", expr (hg_range x).1, ",", expr (hg_range x).2, ",", expr norm_nonneg c, "]"] },
        have [ident h₁] [":", expr «expr = »(«expr * »((2 : exprℝ()), «expr∥ ∥»(c)), bit0 «expr∥ ∥»(c))] [":=", expr by simpa [] [] [] [] [] ["using", expr add_mul (1 : exprℝ()) 1 «expr∥ ∥»(c)]],
        simp [] [] [] ["[", expr hFu, ",", expr norm_smul, ",", expr h₀, ",", "<-", expr h₁, ",", expr g_norm x, "]"] [] [] },
      { simp [] [] [] ["[", expr hgF hF, ",", expr Fs hF, "]"] [] [] } },
    { have [] [":", expr «expr ∉ »(x, s)] [":=", expr λ h, hu (su h)],
      simp [] [] [] ["[", expr hgu hu, ",", expr this, "]"] [] [] } },
  have [ident gc_snorm] [":", expr «expr ≤ »(snorm «expr - »(λ
     x, «expr • »(g x, c), s.indicator (λ
      x, c)) p μ, («expr↑ »(«expr * »(«expr∥ ∥₊»(bit0 «expr∥ ∥»(c)), «expr ^ »(«expr * »(2, η), «expr / »(1, p.to_real)))) : «exprℝ≥0∞»()))] [],
  { refine [expr (snorm_mono_ae (filter.eventually_of_forall gc_bd)).trans _],
    rw [expr snorm_indicator_const (u_open.sdiff F_closed).measurable_set hp₀.ne' hp] [],
    push_cast ["[", "<-", expr ennreal.coe_rpow_of_nonneg _ hp₀', "]"] [],
    exact [expr ennreal.mul_left_mono (ennreal.rpow_left_monotone_of_nonneg hp₀' h_μ_sdiff)] },
  have [ident gc_cont] [":", expr continuous (λ x, «expr • »(g x, c))] [":=", expr g.continuous.smul continuous_const],
  have [ident gc_mem_ℒp] [":", expr mem_ℒp (λ x, «expr • »(g x, c)) p μ] [],
  { have [] [":", expr mem_ℒp «expr - »(λ
      x, «expr • »(g x, c), s.indicator (λ
       x, c)) p μ] [":=", expr ⟨(gc_cont.ae_measurable μ).sub (measurable_const.indicator hs).ae_measurable, gc_snorm.trans_lt ennreal.coe_lt_top⟩],
    simpa [] [] [] [] [] ["using", expr this.add (mem_ℒp_indicator_const p hs c (or.inr hsμ.ne))] },
  refine [expr ⟨gc_mem_ℒp.to_Lp _, _, _⟩],
  { rw [expr mem_closed_ball_iff_norm] [],
    refine [expr le_trans _ hη_le],
    rw ["[", expr simple_func.coe_indicator_const, ",", expr indicator_const_Lp, ",", "<-", expr mem_ℒp.to_Lp_sub, ",", expr Lp.norm_to_Lp, "]"] [],
    exact [expr ennreal.to_real_le_coe_of_le_coe gc_snorm] },
  { rw ["[", expr set_like.mem_coe, ",", expr mem_bounded_continuous_function_iff, "]"] [],
    refine [expr ⟨bounded_continuous_function.of_normed_group _ gc_cont «expr∥ ∥»(c) _, rfl⟩],
    intros [ident x],
    have [ident h₀] [":", expr «expr ≤ »(«expr * »(g x, «expr∥ ∥»(c)), «expr∥ ∥»(c))] [],
    { nlinarith [] [] ["[", expr (hg_range x).1, ",", expr (hg_range x).2, ",", expr norm_nonneg c, "]"] },
    simp [] [] [] ["[", expr norm_smul, ",", expr g_norm x, ",", expr h₀, "]"] [] [] }
end

end MeasureTheory.lp

variable(𝕜 : Type _)[MeasurableSpace 𝕜][NormedField 𝕜][OpensMeasurableSpace 𝕜][NormedAlgebra ℝ 𝕜][NormedSpace 𝕜 E]

namespace BoundedContinuousFunction

-- error in MeasureTheory.Function.ContinuousMapDense: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem to_Lp_dense_range
[μ.weakly_regular]
[is_finite_measure μ] : dense_range «expr⇑ »((to_Lp p μ 𝕜 : «expr →L[ ] »(«expr →ᵇ »(α, E), 𝕜, Lp E p μ))) :=
begin
  haveI [] [":", expr normed_space exprℝ() E] [":=", expr restrict_scalars.normed_space exprℝ() 𝕜 E],
  rw [expr dense_range_iff_closure_range] [],
  suffices [] [":", expr «expr = »((to_Lp p μ 𝕜 : «expr →L[ ] »(_, 𝕜, Lp E p μ)).range.to_add_subgroup.topological_closure, «expr⊤»())],
  { exact [expr congr_arg coe this] },
  simp [] [] [] ["[", expr range_to_Lp p μ, ",", expr measure_theory.Lp.bounded_continuous_function_dense E hp, "]"] [] []
end

end BoundedContinuousFunction

namespace ContinuousMap

-- error in MeasureTheory.Function.ContinuousMapDense: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem to_Lp_dense_range
[compact_space α]
[μ.weakly_regular]
[is_finite_measure μ] : dense_range «expr⇑ »((to_Lp p μ 𝕜 : «expr →L[ ] »(«exprC( , )»(α, E), 𝕜, Lp E p μ))) :=
begin
  haveI [] [":", expr normed_space exprℝ() E] [":=", expr restrict_scalars.normed_space exprℝ() 𝕜 E],
  rw [expr dense_range_iff_closure_range] [],
  suffices [] [":", expr «expr = »((to_Lp p μ 𝕜 : «expr →L[ ] »(_, 𝕜, Lp E p μ)).range.to_add_subgroup.topological_closure, «expr⊤»())],
  { exact [expr congr_arg coe this] },
  simp [] [] [] ["[", expr range_to_Lp p μ, ",", expr measure_theory.Lp.bounded_continuous_function_dense E hp, "]"] [] []
end

end ContinuousMap

