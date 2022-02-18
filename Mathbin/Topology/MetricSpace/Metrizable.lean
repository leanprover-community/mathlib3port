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

variable (X : Type _) [TopologicalSpace X] [NormalSpace X] [SecondCountableTopology X]

/-- A normal topological space with second countable topology can be embedded into `l^∞ = ℕ →ᵇ ℝ`.
-/
theorem exists_embedding_l_infty : ∃ f : X → ℕ →ᵇ ℝ, Embedding f := by
  rcases exists_countable_basis X with ⟨B, hBc, -, hB⟩
  set s : Set (Set X × Set X) := { UV ∈ B ×ˢ B | Closure UV.1 ⊆ UV.2 }
  have : Encodable s := ((hBc.prod hBc).mono (inter_subset_left _ _)).toEncodable
  let this' : TopologicalSpace s := ⊥
  have : DiscreteTopology s := ⟨rfl⟩
  suffices ∃ f : X → s →ᵇ ℝ, Embedding f by
    rcases this with ⟨f, hf⟩
    exact
      ⟨fun x => (f x).extend (Encodable.encode' s) 0,
        (BoundedContinuousFunction.isometry_extend (Encodable.encode' s) (0 : ℕ →ᵇ ℝ)).Embedding.comp hf⟩
  have hd : ∀ UV : s, Disjoint (Closure UV.1.1) (UV.1.2ᶜ) := fun UV =>
    disjoint_compl_right.mono_right (compl_subset_compl.2 UV.2.2)
  obtain ⟨ε, ε01, hε⟩ : ∃ ε : s → ℝ, (∀ UV, ε UV ∈ Ioc (0 : ℝ) 1) ∧ tendsto ε cofinite (𝓝 0) := by
    rcases posSumOfEncodable zero_lt_one s with ⟨ε, ε0, c, hεc, hc1⟩
    refine' ⟨ε, fun UV => ⟨ε0 UV, _⟩, hεc.summable.tendsto_cofinite_zero⟩
    exact ((le_has_sum hεc UV) fun _ _ => (ε0 _).le).trans hc1
  have : ∀ UV : s, ∃ f : C(X, ℝ), eq_on f 0 UV.1.1 ∧ eq_on f (fun _ => ε UV) (UV.1.2ᶜ) ∧ ∀ x, f x ∈ Icc 0 (ε UV) := by
    intro UV
    rcases exists_continuous_zero_one_of_closed is_closed_closure (hB.is_open UV.2.1.2).is_closed_compl (hd UV) with
      ⟨f, hf₀, hf₁, hf01⟩
    exact
      ⟨ε UV • f, fun x hx => by
        simp [hf₀ (subset_closure hx)], fun x hx => by
        simp [hf₁ hx], fun x => ⟨mul_nonneg (ε01 _).1.le (hf01 _).1, mul_le_of_le_one_right (ε01 _).1.le (hf01 _).2⟩⟩
  choose f hf0 hfε hf0ε
  have hf01 : ∀ UV x, f UV x ∈ Icc (0 : ℝ) 1 := fun UV x => Icc_subset_Icc_right (ε01 _).2 (hf0ε _ _)
  set F : X → s →ᵇ ℝ := fun x =>
    ⟨⟨fun UV => f UV x, continuous_of_discrete_topology⟩, 1, fun UV₁ UV₂ =>
      Real.dist_le_of_mem_Icc_01 (hf01 _ _) (hf01 _ _)⟩
  have hF : ∀ x UV, F x UV = f UV x := fun _ _ => rfl
  refine' ⟨F, Embedding.mk' _ (fun x y hxy => _) fun x => le_antisymmₓ _ _⟩
  · refine' not_not.1 fun Hne => _
    rcases hB.mem_nhds_iff.1 (is_open_ne.mem_nhds Hne) with ⟨V, hVB, hxV, hVy⟩
    rcases hB.exists_closure_subset (hB.mem_nhds hVB hxV) with ⟨U, hUB, hxU, hUV⟩
    set UV : ↥s := ⟨(U, V), ⟨hUB, hVB⟩, hUV⟩
    apply (ε01 UV).1.Ne
    calc (0 : ℝ) = F x UV := (hf0 UV hxU).symm _ = F y UV := by
        rw [hxy]_ = ε UV := hfε UV fun h : y ∈ V => hVy h rfl
    
  · refine' ((nhds_basis_ball.comap _).le_basis_iff hB.nhds_has_basis).2 _
    rintro V ⟨hVB, hxV⟩
    rcases hB.exists_closure_subset (hB.mem_nhds hVB hxV) with ⟨U, hUB, hxU, hUV⟩
    set UV : ↥s := ⟨(U, V), ⟨hUB, hVB⟩, hUV⟩
    refine' ⟨ε UV, (ε01 UV).1, fun y hy : dist (F y) (F x) < ε UV => _⟩
    replace hy : dist (F y UV) (F x UV) < ε UV
    exact (BoundedContinuousFunction.dist_coe_le_dist _).trans_lt hy
    contrapose! hy
    rw [hF, hF, hfε UV hy, hf0 UV hxU, Pi.zero_apply, dist_zero_right]
    exact le_abs_self _
    
  · refine' (nhds_basis_closed_ball.comap _).ge_iff.2 fun δ δ0 => _
    have h_fin : finite { UV : s | δ ≤ ε UV } := by
      simpa only [← not_ltₓ] using hε (gt_mem_nhds δ0)
    have : ∀ᶠ y in 𝓝 x, ∀ UV, δ ≤ ε UV → dist (F y UV) (F x UV) ≤ δ := by
      refine' (eventually_all_finite h_fin).2 fun UV hUV => _
      exact (f UV).Continuous.Tendsto x (closed_ball_mem_nhds _ δ0)
    refine' this.mono fun y hy => (BoundedContinuousFunction.dist_le δ0.le).2 fun UV => _
    cases' le_totalₓ δ (ε UV) with hle hle
    exacts[hy _ hle,
      (Real.dist_le_of_mem_Icc (hf0ε _ _) (hf0ε _ _)).trans
        (by
          rwa [sub_zero])]
    

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

