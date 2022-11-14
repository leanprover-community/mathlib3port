/-
Copyright (c) 2022 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker
-/
import Mathbin.Topology.UniformSpace.UniformConvergenceTopology
import Mathbin.Analysis.LocallyConvex.Bounded
import Mathbin.Topology.Algebra.FilterBasis

/-!
# Algebraic facts about the topology of uniform convergence

This file contains algebraic compatibility results about the uniform structure of uniform
convergence / `𝔖`-convergence. They will mostly be useful for defining strong topologies on the
space of continuous linear maps between two topological vector spaces.

## Main statements

* `uniform_convergence.uniform_group` : if `G` is a uniform group, then the uniform structure of
  uniform convergence makes `α → G` a uniform group
* `uniform_convergence_on.uniform_group` : if `G` is a uniform group, then the uniform structure of
  `𝔖`-convergence, for any `𝔖 : set (set α)`, makes `α → G` a uniform group.
* `uniform_convergence_on.has_continuous_smul_of_image_bounded` : let `E` be a TVS,
  `𝔖 : set (set α)` and `H` a submodule of `α → E`. If the image of any `S ∈ 𝔖` by any `u ∈ H` is
  bounded (in the sense of `bornology.is_vonN_bounded`), then `H`, equipped with the topology of
  `𝔖`-convergence, is a TVS.

## TODO

* `uniform_convergence_on.has_continuous_smul_of_image_bounded` unnecessarily asks for `𝔖` to be
  nonempty and directed. This will be easy to solve once we know that replacing `𝔖` by its
  ***noncovering*** bornology (i.e ***not*** what `bornology` currently refers to in mathlib)
  doesn't change the topology.

## References

* [N. Bourbaki, *General Topology, Chapter X*][bourbaki1966]
* [N. Bourbaki, *Topological Vector Spaces*][bourbaki1987]

## Tags

uniform convergence, strong dual

-/


open Filter

open TopologicalSpace Pointwise

section Group

variable {α G ι : Type _} [Group G] [UniformSpace G] [UniformGroup G] {𝔖 : Set <| Set α}

attribute [-instance] PiCat.uniformSpace

attribute [-instance] PiCat.topologicalSpace

/-- If `G` is a uniform group, then the uniform structure of uniform convergence makes `α → G`
a uniform group as well. -/
@[to_additive
      "If `G` is a uniform additive group, then the uniform structure of uniform\nconvergence makes `α → G` a uniform additive group as well."]
protected theorem UniformConvergence.uniform_group : @UniformGroup (α → G) (UniformConvergence.uniformSpace α G) _ := by
  -- Since `(/) : G × G → G` is uniformly continuous,
  -- `uniform_convergence.postcomp_uniform_continuous` tells us that
  -- `((/) ∘ —) : (α → G × G) → (α → G)` is uniformly continuous too. By precomposing with
  -- `uniform_convergence.uniform_equiv_prod_arrow`, this gives that
  -- `(/) : (α → G) × (α → G) → (α → G)` is also uniformly continuous
  letI : UniformSpace (α → G) := UniformConvergence.uniformSpace α G
  letI : UniformSpace (α → G × G) := UniformConvergence.uniformSpace α (G × G)
  exact
    ⟨(UniformConvergence.postcomp_uniform_continuous uniform_continuous_div).comp
        uniform_convergence.uniform_equiv_prod_arrow.symm.uniform_continuous⟩
#align uniform_convergence.uniform_group UniformConvergence.uniform_group

@[to_additive]
protected theorem UniformConvergence.has_basis_nhds_one_of_basis {p : ι → Prop} {b : ι → Set G}
    (h : (𝓝 1 : Filter G).HasBasis p b) :
    (@nhds (α → G) (UniformConvergence.topologicalSpace α G) 1).HasBasis p fun i => { f : α → G | ∀ x, f x ∈ b i } := by
  have := h.comap fun p : G × G => p.2 / p.1
  rw [← uniformity_eq_comap_nhds_one] at this
  convert UniformConvergence.has_basis_nhds_of_basis α _ 1 this
  ext (i f)
  simp [UniformConvergence.gen]
#align uniform_convergence.has_basis_nhds_one_of_basis UniformConvergence.has_basis_nhds_one_of_basis

@[to_additive]
protected theorem UniformConvergence.has_basis_nhds_one :
    (@nhds (α → G) (UniformConvergence.topologicalSpace α G) 1).HasBasis (fun V : Set G => V ∈ (𝓝 1 : Filter G))
      fun V => { f : α → G | ∀ x, f x ∈ V } :=
  UniformConvergence.has_basis_nhds_one_of_basis (basis_sets _)
#align uniform_convergence.has_basis_nhds_one UniformConvergence.has_basis_nhds_one

/-- Let `𝔖 : set (set α)`. If `G` is a uniform group, then the uniform structure of
`𝔖`-convergence makes `α → G` a uniform group as well. -/
@[to_additive
      "Let `𝔖 : set (set α)`. If `G` is a uniform additive group, then the uniform\nstructure of  `𝔖`-convergence makes `α → G` a uniform additive group as well. "]
protected theorem UniformConvergenceOn.uniform_group :
    @UniformGroup (α → G) (UniformConvergenceOn.uniformSpace α G 𝔖) _ := by
  -- Since `(/) : G × G → G` is uniformly continuous,
  -- `uniform_convergence_on.postcomp_uniform_continuous` tells us that
  -- `((/) ∘ —) : (α → G × G) → (α → G)` is uniformly continuous too. By precomposing with
  -- `uniform_convergence_on.uniform_equiv_prod_arrow`, this gives that
  -- `(/) : (α → G) × (α → G) → (α → G)` is also uniformly continuous
  letI : UniformSpace (α → G) := UniformConvergenceOn.uniformSpace α G 𝔖
  letI : UniformSpace (α → G × G) := UniformConvergenceOn.uniformSpace α (G × G) 𝔖
  exact
    ⟨(UniformConvergenceOn.postcomp_uniform_continuous uniform_continuous_div).comp
        uniform_convergence_on.uniform_equiv_prod_arrow.symm.uniform_continuous⟩
#align uniform_convergence_on.uniform_group UniformConvergenceOn.uniform_group

@[to_additive]
protected theorem UniformConvergenceOn.has_basis_nhds_one_of_basis (𝔖 : Set <| Set α) (h𝔖₁ : 𝔖.Nonempty)
    (h𝔖₂ : DirectedOn (· ⊆ ·) 𝔖) {p : ι → Prop} {b : ι → Set G} (h : (𝓝 1 : Filter G).HasBasis p b) :
    (@nhds (α → G) (UniformConvergenceOn.topologicalSpace α G 𝔖) 1).HasBasis (fun Si : Set α × ι => Si.1 ∈ 𝔖 ∧ p Si.2)
      fun Si => { f : α → G | ∀ x ∈ Si.1, f x ∈ b Si.2 } :=
  by
  have := h.comap fun p : G × G => p.1 / p.2
  rw [← uniformity_eq_comap_nhds_one_swapped] at this
  convert UniformConvergenceOn.has_basis_nhds_of_basis α _ 𝔖 1 h𝔖₁ h𝔖₂ this
  ext (i f)
  simp [UniformConvergenceOn.gen]
#align uniform_convergence_on.has_basis_nhds_one_of_basis UniformConvergenceOn.has_basis_nhds_one_of_basis

@[to_additive]
protected theorem UniformConvergenceOn.has_basis_nhds_one (𝔖 : Set <| Set α) (h𝔖₁ : 𝔖.Nonempty)
    (h𝔖₂ : DirectedOn (· ⊆ ·) 𝔖) :
    (@nhds (α → G) (UniformConvergenceOn.topologicalSpace α G 𝔖) 1).HasBasis
      (fun SV : Set α × Set G => SV.1 ∈ 𝔖 ∧ SV.2 ∈ (𝓝 1 : Filter G)) fun SV => { f : α → G | ∀ x ∈ SV.1, f x ∈ SV.2 } :=
  UniformConvergenceOn.has_basis_nhds_one_of_basis 𝔖 h𝔖₁ h𝔖₂ (basis_sets _)
#align uniform_convergence_on.has_basis_nhds_one UniformConvergenceOn.has_basis_nhds_one

end Group

section Module

variable (𝕜 α E H : Type _) {hom : Type _} [NormedField 𝕜] [AddCommGroup H] [Module 𝕜 H] [AddCommGroup E] [Module 𝕜 E]
  [LinearMapClass hom 𝕜 H (α → E)] [TopologicalSpace H] [UniformSpace E] [UniformAddGroup E] [HasContinuousSmul 𝕜 E]
  {𝔖 : Set <| Set α}

attribute [-instance] PiCat.uniformSpace

attribute [-instance] PiCat.topologicalSpace

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/-- Let `E` be a TVS, `𝔖 : set (set α)` and `H` a submodule of `α → E`. If the image of any `S ∈ 𝔖`
by any `u ∈ H` is bounded (in the sense of `bornology.is_vonN_bounded`), then `H`, equipped with
the topology of `𝔖`-convergence, is a TVS.

For convenience, we don't literally ask for `H : submodule (α → E)`. Instead, we prove the result
for any vector space `H` equipped with a linear inducing to `α → E`, which is often easier to use.
We also state the `submodule` version as
`uniform_convergence_on.has_continuous_smul_submodule_of_image_bounded`. -/
theorem UniformConvergenceOn.has_continuous_smul_induced_of_image_bounded (h𝔖₁ : 𝔖.Nonempty)
    (h𝔖₂ : DirectedOn (· ⊆ ·) 𝔖) (φ : hom) (hφ : @Inducing _ _ _ (UniformConvergenceOn.topologicalSpace α E 𝔖) φ)
    (h : ∀ u : H, ∀ s ∈ 𝔖, Bornology.IsVonNBounded 𝕜 ((φ u : α → E) '' s)) : HasContinuousSmul 𝕜 H := by
  letI : UniformSpace (α → E) := UniformConvergenceOn.uniformSpace α E 𝔖
  haveI : UniformAddGroup (α → E) := UniformConvergenceOn.uniform_add_group
  have : TopologicalAddGroup H := by
    rw [hφ.induced]
    exact topological_add_group_induced φ
  have : (𝓝 0 : Filter H).HasBasis _ _ := by
    rw [hφ.induced, nhds_induced, map_zero]
    exact (UniformConvergenceOn.has_basis_nhds_zero 𝔖 h𝔖₁ h𝔖₂).comap φ
  refine' HasContinuousSmul.of_basis_zero this _ _ _
  · rintro ⟨S, V⟩ ⟨hS, hV⟩
    have : tendsto (fun kx : 𝕜 × E => kx.1 • kx.2) (𝓝 (0, 0)) (𝓝 <| (0 : 𝕜) • 0) := continuous_smul.tendsto (0 : 𝕜 × E)
    rw [zero_smul, nhds_prod_eq] at this
    have := this hV
    rw [mem_map, mem_prod_iff] at this
    rcases this with ⟨U, hU, W, hW, hUW⟩
    refine' ⟨U, hU, ⟨S, W⟩, ⟨hS, hW⟩, _⟩
    rw [Set.smul_subset_iff]
    intro a ha u hu x hx
    rw [SmulHomClass.map_smul]
    exact hUW (⟨ha, hu x hx⟩ : (a, φ u x) ∈ U ×ˢ W)
    
  · rintro a ⟨S, V⟩ ⟨hS, hV⟩
    have : tendsto (fun x : E => a • x) (𝓝 0) (𝓝 <| a • 0) := tendsto_id.const_smul a
    rw [smul_zero] at this
    refine' ⟨⟨S, (· • ·) a ⁻¹' V⟩, ⟨hS, this hV⟩, fun f hf x hx => _⟩
    rw [SmulHomClass.map_smul]
    exact hf x hx
    
  · rintro u ⟨S, V⟩ ⟨hS, hV⟩
    rcases h u S hS hV with ⟨r, hrpos, hr⟩
    rw [Metric.eventually_nhds_iff_ball]
    refine' ⟨r⁻¹, inv_pos.mpr hrpos, fun a ha x hx => _⟩
    by_cases ha0:a = 0
    · rw [ha0]
      simp [mem_of_mem_nhds hV]
      
    · rw [mem_ball_zero_iff] at ha
      rw [SmulHomClass.map_smul, Pi.smul_apply]
      have : φ u x ∈ a⁻¹ • V := by
        have ha0 : 0 < ∥a∥ := norm_pos_iff.mpr ha0
        refine' (hr a⁻¹ _) (Set.mem_image_of_mem (φ u) hx)
        rw [norm_inv, le_inv hrpos ha0]
        exact ha.le
      rwa [Set.mem_inv_smul_set_iff₀ ha0] at this
      
    
#align
  uniform_convergence_on.has_continuous_smul_induced_of_image_bounded UniformConvergenceOn.has_continuous_smul_induced_of_image_bounded

/-- Let `E` be a TVS, `𝔖 : set (set α)` and `H` a submodule of `α → E`. If the image of any `S ∈ 𝔖`
by any `u ∈ H` is bounded (in the sense of `bornology.is_vonN_bounded`), then `H`, equipped with
the topology of `𝔖`-convergence, is a TVS.

If you have a hard time using this lemma, try the one above instead. -/
theorem UniformConvergenceOn.has_continuous_smul_submodule_of_image_bounded (h𝔖₁ : 𝔖.Nonempty)
    (h𝔖₂ : DirectedOn (· ⊆ ·) 𝔖) (H : Submodule 𝕜 (α → E)) (h : ∀ u ∈ H, ∀ s ∈ 𝔖, Bornology.IsVonNBounded 𝕜 (u '' s)) :
    @HasContinuousSmul 𝕜 H _ _ ((UniformConvergenceOn.topologicalSpace α E 𝔖).induced (coe : H → α → E)) := by
  letI : UniformSpace (α → E) := UniformConvergenceOn.uniformSpace α E 𝔖
  haveI : UniformAddGroup (α → E) := UniformConvergenceOn.uniform_add_group
  haveI : TopologicalAddGroup H := topological_add_group_induced (linear_map.id.dom_restrict H : H →ₗ[𝕜] α → E)
  exact
    UniformConvergenceOn.has_continuous_smul_induced_of_image_bounded 𝕜 α E H h𝔖₁ h𝔖₂
      (linear_map.id.dom_restrict H : H →ₗ[𝕜] α → E) inducing_coe fun ⟨u, hu⟩ => h u hu
#align
  uniform_convergence_on.has_continuous_smul_submodule_of_image_bounded UniformConvergenceOn.has_continuous_smul_submodule_of_image_bounded

end Module

