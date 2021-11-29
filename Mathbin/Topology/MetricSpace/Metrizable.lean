import Mathbin.Topology.UrysohnsLemma 
import Mathbin.Topology.ContinuousFunction.Bounded

/-!
# Metrizability of a normal topological space with second countable topology

In this file we show that a normal topological space with second countable topology `X` is
metrizable: there exists a metric space structure that generates the same topology.

First we prove that `X` can be embedded into `l^∞`, then use this embedding to pull back the metric
space structure.
-/


open Set Filter Metric

open_locale BoundedContinuousFunction Filter TopologicalSpace

namespace TopologicalSpace

variable (X : Type _) [TopologicalSpace X] [NormalSpace X] [second_countable_topology X]

-- error in Topology.MetricSpace.Metrizable: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- A normal topological space with second countable topology can be embedded into `l^∞ = ℕ →ᵇ ℝ`.
-/ theorem exists_embedding_l_infty : «expr∃ , »((f : X → «expr →ᵇ »(exprℕ(), exprℝ())), embedding f) :=
begin
  rcases [expr exists_countable_basis X, "with", "⟨", ident B, ",", ident hBc, ",", "-", ",", ident hB, "⟩"],
  set [] [ident s] [":", expr set «expr × »(set X, set X)] [":="] [expr {UV ∈ B.prod B | «expr ⊆ »(closure UV.1, UV.2)}] [],
  haveI [] [":", expr encodable s] [":=", expr ((hBc.prod hBc).mono (inter_subset_left _ _)).to_encodable],
  letI [] [":", expr topological_space s] [":=", expr «expr⊥»()],
  haveI [] [":", expr discrete_topology s] [":=", expr ⟨rfl⟩],
  suffices [] [":", expr «expr∃ , »((f : X → «expr →ᵇ »(s, exprℝ())), embedding f)],
  { rcases [expr this, "with", "⟨", ident f, ",", ident hf, "⟩"],
    exact [expr ⟨λ
      x, (f x).extend (encodable.encode' s) 0, (bounded_continuous_function.isometry_extend (encodable.encode' s) (0 : «expr →ᵇ »(exprℕ(), exprℝ()))).embedding.comp hf⟩] },
  have [ident hd] [":", expr ∀
   UV : s, disjoint (closure UV.1.1) «expr ᶜ»(UV.1.2)] [":=", expr λ
   UV, disjoint_compl_right.mono_right (compl_subset_compl.2 UV.2.2)],
  obtain ["⟨", ident ε, ",", ident ε01, ",", ident hε, "⟩", ":", expr «expr∃ , »((ε : s → exprℝ()), «expr ∧ »(∀
     UV, «expr ∈ »(ε UV, Ioc (0 : exprℝ()) 1), tendsto ε cofinite (expr𝓝() 0)))],
  { rcases [expr pos_sum_of_encodable zero_lt_one s, "with", "⟨", ident ε, ",", ident ε0, ",", ident c, ",", ident hεc, ",", ident hc1, "⟩"],
    refine [expr ⟨ε, λ UV, ⟨ε0 UV, _⟩, hεc.summable.tendsto_cofinite_zero⟩],
    exact [expr «expr $ »(le_has_sum hεc UV, λ _ _, (ε0 _).le).trans hc1] },
  have [] [":", expr ∀
   UV : s, «expr∃ , »((f : «exprC( , )»(X, exprℝ())), «expr ∧ »(eq_on f 0 UV.1.1, «expr ∧ »(eq_on f (λ
       _, ε UV) «expr ᶜ»(UV.1.2), ∀ x, «expr ∈ »(f x, Icc 0 (ε UV)))))] [],
  { intro [ident UV],
    rcases [expr exists_continuous_zero_one_of_closed is_closed_closure (hB.is_open UV.2.1.2).is_closed_compl (hd UV), "with", "⟨", ident f, ",", ident hf₀, ",", ident hf₁, ",", ident hf01, "⟩"],
    exact [expr ⟨«expr • »(ε UV, f), λ
      x
      hx, by simp [] [] [] ["[", expr hf₀ (subset_closure hx), "]"] [] [], λ
      x
      hx, by simp [] [] [] ["[", expr hf₁ hx, "]"] [] [], λ
      x, ⟨mul_nonneg (ε01 _).1.le (hf01 _).1, mul_le_of_le_one_right (ε01 _).1.le (hf01 _).2⟩⟩] },
  choose [] [ident f] [ident hf0, ident hfε, ident hf0ε] [],
  have [ident hf01] [":", expr ∀ UV x, «expr ∈ »(f UV x, Icc (0 : exprℝ()) 1)] [],
  from [expr λ UV x, Icc_subset_Icc_right (ε01 _).2 (hf0ε _ _)],
  set [] [ident F] [":", expr X → «expr →ᵇ »(s, exprℝ())] [":="] [expr λ
   x, ⟨⟨λ
     UV, f UV x, continuous_of_discrete_topology⟩, 1, λ UV₁ UV₂, real.dist_le_of_mem_Icc_01 (hf01 _ _) (hf01 _ _)⟩] [],
  have [ident hF] [":", expr ∀ x UV, «expr = »(F x UV, f UV x)] [":=", expr λ _ _, rfl],
  refine [expr ⟨F, embedding.mk' _ (λ x y hxy, _) (λ x, le_antisymm _ _)⟩],
  { refine [expr not_not.1 (λ Hne, _)],
    rcases [expr hB.mem_nhds_iff.1 (is_open_ne.mem_nhds Hne), "with", "⟨", ident V, ",", ident hVB, ",", ident hxV, ",", ident hVy, "⟩"],
    rcases [expr hB.exists_closure_subset (hB.mem_nhds hVB hxV), "with", "⟨", ident U, ",", ident hUB, ",", ident hxU, ",", ident hUV, "⟩"],
    set [] [ident UV] [":", expr «expr↥ »(s)] [":="] [expr ⟨(U, V), ⟨hUB, hVB⟩, hUV⟩] [],
    apply [expr (ε01 UV).1.ne],
    calc
      «expr = »((0 : exprℝ()), F x UV) : (hf0 UV hxU).symm
      «expr = »(..., F y UV) : by rw [expr hxy] []
      «expr = »(..., ε UV) : hfε UV (λ h : «expr ∈ »(y, V), hVy h rfl) },
  { refine [expr ((nhds_basis_ball.comap _).le_basis_iff hB.nhds_has_basis).2 _],
    rintro [ident V, "⟨", ident hVB, ",", ident hxV, "⟩"],
    rcases [expr hB.exists_closure_subset (hB.mem_nhds hVB hxV), "with", "⟨", ident U, ",", ident hUB, ",", ident hxU, ",", ident hUV, "⟩"],
    set [] [ident UV] [":", expr «expr↥ »(s)] [":="] [expr ⟨(U, V), ⟨hUB, hVB⟩, hUV⟩] [],
    refine [expr ⟨ε UV, (ε01 UV).1, λ (y) (hy : «expr < »(dist (F y) (F x), ε UV)), _⟩],
    replace [ident hy] [":", expr «expr < »(dist (F y UV) (F x UV), ε UV)] [],
    from [expr (bounded_continuous_function.dist_coe_le_dist _).trans_lt hy],
    contrapose ["!"] [ident hy],
    rw ["[", expr hF, ",", expr hF, ",", expr hfε UV hy, ",", expr hf0 UV hxU, ",", expr pi.zero_apply, ",", expr dist_zero_right, "]"] [],
    exact [expr le_abs_self _] },
  { refine [expr (nhds_basis_closed_ball.comap _).ge_iff.2 (λ δ δ0, _)],
    have [ident h_fin] [":", expr finite {UV : s | «expr ≤ »(δ, ε UV)}] [],
    by simpa [] [] ["only"] ["[", "<-", expr not_lt, "]"] [] ["using", expr hε (gt_mem_nhds δ0)],
    have [] [":", expr «expr∀ᶠ in , »((y), expr𝓝() x, ∀
      UV, «expr ≤ »(δ, ε UV) → «expr ≤ »(dist (F y UV) (F x UV), δ))] [],
    { refine [expr (eventually_all_finite h_fin).2 (λ UV hUV, _)],
      exact [expr (f UV).continuous.tendsto x (closed_ball_mem_nhds _ δ0)] },
    refine [expr this.mono (λ y hy, «expr $ »((bounded_continuous_function.dist_le δ0.le).2, λ UV, _))],
    cases [expr le_total δ (ε UV)] ["with", ident hle, ident hle],
    exacts ["[", expr hy _ hle, ",", expr (real.dist_le_of_mem_Icc (hf0ε _ _) (hf0ε _ _)).trans (by rwa [expr sub_zero] []), "]"] }
end

/-- A normal topological space with second countable topology `X` is metrizable: there exists a
metric space structure that generates the same topology. This definition provides a `metric_space`
instance such that the corresponding `topological_space X` instance is definitionally equal
to the original one. -/
@[reducible]
noncomputable def to_metric_space : MetricSpace X :=
  @MetricSpace.replaceUniformity X
    ((UniformSpace.comap (exists_embedding_l_infty X).some inferInstance).replaceTopology
      (exists_embedding_l_infty X).some_spec.induced)
    (MetricSpace.induced (exists_embedding_l_infty X).some (exists_embedding_l_infty X).some_spec.inj inferInstance) rfl

end TopologicalSpace

