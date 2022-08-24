/-
Copyright (c) 2022 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker
-/
import Mathbin.Analysis.NormedSpace.OperatorNorm
import Mathbin.Analysis.LocallyConvex.Bounded

/-!
# Compact operators

In this file we define compact linear operators between two topological vector spaces (TVS).

## Main definitions

* `is_compact_operator` : predicate for compact operators

## Main statements

* `is_compact_operator_iff_is_compact_closure_image_closed_ball` : the usual characterization of
  compact operators from a normed space to a T2 TVS.
* `is_compact_operator.comp_clm` : precomposing a compact operator by a continuous linear map gives
  a compact operator
* `is_compact_operator.clm_comp` : postcomposing a compact operator by a continuous linear map
  gives a compact operator
* `is_compact_operator.continuous` : compact operators are automatically continuous
* `is_closed_set_of_is_compact_operator` : the set of compact operators is closed for the operator
  norm

## Implementation details

We define `is_compact_operator` as a predicate, because the space of compact operators inherits all
of its structure from the space of continuous linear maps (e.g we want to have the usual operator
norm on compact operators).

The two natural options then would be to make it a predicate over linear maps or continuous linear
maps. Instead we define it as a predicate over bare functions, although it really only makes sense
for linear functions, because Lean is really good at finding coercions to bare functions (whereas
coercing from continuous linear maps to linear maps often needs type ascriptions).

## TODO

Once we have the strong operator topology on spaces of linear maps between two TVSs,
`is_closed_set_of_is_compact_operator` should be generalized to this setup.

## References

* Bourbaki, *Spectral Theory*, chapters 3 to 5, to be published (2022)

## Tags

Compact operator
-/


open Function Set Filter Bornology Metric

open Pointwise BigOperators TopologicalSpace

/-- A compact operator between two topological vector spaces. This definition is usually
given as "there exists a neighborhood of zero whose image is contained in a compact set",
but we choose a definition which involves fewer existential quantifiers and replaces images
with preimages.

We prove the equivalence in `is_compact_operator_iff_exists_mem_nhds_image_subset_compact`. -/
def IsCompactOperator {M₁ M₂ : Type _} [Zero M₁] [TopologicalSpace M₁] [TopologicalSpace M₂] (f : M₁ → M₂) : Prop :=
  ∃ K, IsCompact K ∧ f ⁻¹' K ∈ (𝓝 0 : Filter M₁)

theorem is_compact_operator_zero {M₁ M₂ : Type _} [Zero M₁] [TopologicalSpace M₁] [TopologicalSpace M₂] [Zero M₂] :
    IsCompactOperator (0 : M₁ → M₂) :=
  ⟨{0}, is_compact_singleton, mem_of_superset univ_mem fun x _ => rfl⟩

section Characterizations

section

variable {R₁ R₂ : Type _} [Semiringₓ R₁] [Semiringₓ R₂] {σ₁₂ : R₁ →+* R₂} {M₁ M₂ : Type _} [TopologicalSpace M₁]
  [AddCommMonoidₓ M₁] [TopologicalSpace M₂]

theorem is_compact_operator_iff_exists_mem_nhds_image_subset_compact (f : M₁ → M₂) :
    IsCompactOperator f ↔ ∃ V ∈ (𝓝 0 : Filter M₁), ∃ K : Set M₂, IsCompact K ∧ f '' V ⊆ K :=
  ⟨fun ⟨K, hK, hKf⟩ => ⟨f ⁻¹' K, hKf, K, hK, image_preimage_subset _ _⟩, fun ⟨V, hV, K, hK, hVK⟩ =>
    ⟨K, hK, mem_of_superset hV (image_subset_iff.mp hVK)⟩⟩

theorem is_compact_operator_iff_exists_mem_nhds_is_compact_closure_image [T2Space M₂] (f : M₁ → M₂) :
    IsCompactOperator f ↔ ∃ V ∈ (𝓝 0 : Filter M₁), IsCompact (Closure <| f '' V) := by
  rw [is_compact_operator_iff_exists_mem_nhds_image_subset_compact]
  exact
    ⟨fun ⟨V, hV, K, hK, hKV⟩ => ⟨V, hV, compact_closure_of_subset_compact hK hKV⟩, fun ⟨V, hV, hVc⟩ =>
      ⟨V, hV, Closure (f '' V), hVc, subset_closure⟩⟩

end

section Bounded

variable {𝕜₁ 𝕜₂ : Type _} [NontriviallyNormedField 𝕜₁] [SemiNormedRing 𝕜₂] {σ₁₂ : 𝕜₁ →+* 𝕜₂} {M₁ M₂ : Type _}
  [TopologicalSpace M₁] [AddCommMonoidₓ M₁] [TopologicalSpace M₂] [AddCommMonoidₓ M₂] [Module 𝕜₁ M₁] [Module 𝕜₂ M₂]
  [HasContinuousConstSmul 𝕜₂ M₂]

theorem IsCompactOperator.image_subset_compact_of_vonN_bounded {f : M₁ →ₛₗ[σ₁₂] M₂} (hf : IsCompactOperator f)
    {S : Set M₁} (hS : IsVonNBounded 𝕜₁ S) : ∃ K : Set M₂, IsCompact K ∧ f '' S ⊆ K :=
  let ⟨K, hK, hKf⟩ := hf
  let ⟨r, hr, hrS⟩ := hS hKf
  let ⟨c, hc⟩ := NormedField.exists_lt_norm 𝕜₁ r
  let this := ne_zero_of_norm_ne_zero (hr.trans hc).Ne.symm
  ⟨σ₁₂ c • K, hK.Image <| continuous_id.const_smul (σ₁₂ c), by
    rw [image_subset_iff, preimage_smul_setₛₗ _ _ _ f this.is_unit] <;> exact hrS c hc.le⟩

theorem IsCompactOperator.is_compact_closure_image_of_vonN_bounded [T2Space M₂] {f : M₁ →ₛₗ[σ₁₂] M₂}
    (hf : IsCompactOperator f) {S : Set M₁} (hS : IsVonNBounded 𝕜₁ S) : IsCompact (Closure <| f '' S) :=
  let ⟨K, hK, hKf⟩ := hf.image_subset_compact_of_vonN_bounded hS
  compact_closure_of_subset_compact hK hKf

end Bounded

section NormedSpace

variable {𝕜₁ 𝕜₂ : Type _} [NontriviallyNormedField 𝕜₁] [SemiNormedRing 𝕜₂] {σ₁₂ : 𝕜₁ →+* 𝕜₂} {M₁ M₂ M₃ : Type _}
  [SeminormedAddCommGroup M₁] [TopologicalSpace M₂] [AddCommMonoidₓ M₂] [NormedSpace 𝕜₁ M₁] [Module 𝕜₂ M₂]

theorem IsCompactOperator.image_subset_compact_of_bounded [HasContinuousConstSmul 𝕜₂ M₂] {f : M₁ →ₛₗ[σ₁₂] M₂}
    (hf : IsCompactOperator f) {S : Set M₁} (hS : Metric.Bounded S) : ∃ K : Set M₂, IsCompact K ∧ f '' S ⊆ K :=
  hf.image_subset_compact_of_vonN_bounded
    (by
      rwa [NormedSpace.is_vonN_bounded_iff, ← Metric.bounded_iff_is_bounded])

theorem IsCompactOperator.is_compact_closure_image_of_bounded [HasContinuousConstSmul 𝕜₂ M₂] [T2Space M₂]
    {f : M₁ →ₛₗ[σ₁₂] M₂} (hf : IsCompactOperator f) {S : Set M₁} (hS : Metric.Bounded S) :
    IsCompact (Closure <| f '' S) :=
  hf.is_compact_closure_image_of_vonN_bounded
    (by
      rwa [NormedSpace.is_vonN_bounded_iff, ← Metric.bounded_iff_is_bounded])

theorem IsCompactOperator.image_ball_subset_compact [HasContinuousConstSmul 𝕜₂ M₂] {f : M₁ →ₛₗ[σ₁₂] M₂}
    (hf : IsCompactOperator f) (r : ℝ) : ∃ K : Set M₂, IsCompact K ∧ f '' Metric.Ball 0 r ⊆ K :=
  hf.image_subset_compact_of_vonN_bounded (NormedSpace.is_vonN_bounded_ball 𝕜₁ M₁ r)

theorem IsCompactOperator.image_closed_ball_subset_compact [HasContinuousConstSmul 𝕜₂ M₂] {f : M₁ →ₛₗ[σ₁₂] M₂}
    (hf : IsCompactOperator f) (r : ℝ) : ∃ K : Set M₂, IsCompact K ∧ f '' Metric.ClosedBall 0 r ⊆ K :=
  hf.image_subset_compact_of_vonN_bounded (NormedSpace.is_vonN_bounded_closed_ball 𝕜₁ M₁ r)

theorem IsCompactOperator.is_compact_closure_image_ball [HasContinuousConstSmul 𝕜₂ M₂] [T2Space M₂] {f : M₁ →ₛₗ[σ₁₂] M₂}
    (hf : IsCompactOperator f) (r : ℝ) : IsCompact (Closure <| f '' Metric.Ball 0 r) :=
  hf.is_compact_closure_image_of_vonN_bounded (NormedSpace.is_vonN_bounded_ball 𝕜₁ M₁ r)

theorem IsCompactOperator.is_compact_closure_image_closed_ball [HasContinuousConstSmul 𝕜₂ M₂] [T2Space M₂]
    {f : M₁ →ₛₗ[σ₁₂] M₂} (hf : IsCompactOperator f) (r : ℝ) : IsCompact (Closure <| f '' Metric.ClosedBall 0 r) :=
  hf.is_compact_closure_image_of_vonN_bounded (NormedSpace.is_vonN_bounded_closed_ball 𝕜₁ M₁ r)

theorem is_compact_operator_iff_image_ball_subset_compact [HasContinuousConstSmul 𝕜₂ M₂] (f : M₁ →ₛₗ[σ₁₂] M₂) {r : ℝ}
    (hr : 0 < r) : IsCompactOperator f ↔ ∃ K : Set M₂, IsCompact K ∧ f '' Metric.Ball 0 r ⊆ K :=
  ⟨fun hf => hf.image_ball_subset_compact r, fun ⟨K, hK, hKr⟩ =>
    (is_compact_operator_iff_exists_mem_nhds_image_subset_compact f).mpr
      ⟨Metric.Ball 0 r, ball_mem_nhds _ hr, K, hK, hKr⟩⟩

theorem is_compact_operator_iff_image_closed_ball_subset_compact [HasContinuousConstSmul 𝕜₂ M₂] (f : M₁ →ₛₗ[σ₁₂] M₂)
    {r : ℝ} (hr : 0 < r) : IsCompactOperator f ↔ ∃ K : Set M₂, IsCompact K ∧ f '' Metric.ClosedBall 0 r ⊆ K :=
  ⟨fun hf => hf.image_closed_ball_subset_compact r, fun ⟨K, hK, hKr⟩ =>
    (is_compact_operator_iff_exists_mem_nhds_image_subset_compact f).mpr
      ⟨Metric.ClosedBall 0 r, closed_ball_mem_nhds _ hr, K, hK, hKr⟩⟩

theorem is_compact_operator_iff_is_compact_closure_image_ball [HasContinuousConstSmul 𝕜₂ M₂] [T2Space M₂]
    (f : M₁ →ₛₗ[σ₁₂] M₂) {r : ℝ} (hr : 0 < r) : IsCompactOperator f ↔ IsCompact (Closure <| f '' Metric.Ball 0 r) :=
  ⟨fun hf => hf.is_compact_closure_image_ball r, fun hf =>
    (is_compact_operator_iff_exists_mem_nhds_is_compact_closure_image f).mpr ⟨Metric.Ball 0 r, ball_mem_nhds _ hr, hf⟩⟩

theorem is_compact_operator_iff_is_compact_closure_image_closed_ball [HasContinuousConstSmul 𝕜₂ M₂] [T2Space M₂]
    (f : M₁ →ₛₗ[σ₁₂] M₂) {r : ℝ} (hr : 0 < r) :
    IsCompactOperator f ↔ IsCompact (Closure <| f '' Metric.ClosedBall 0 r) :=
  ⟨fun hf => hf.is_compact_closure_image_closed_ball r, fun hf =>
    (is_compact_operator_iff_exists_mem_nhds_is_compact_closure_image f).mpr
      ⟨Metric.ClosedBall 0 r, closed_ball_mem_nhds _ hr, hf⟩⟩

end NormedSpace

end Characterizations

section Operations

variable {R₁ R₂ R₃ R₄ : Type _} [Semiringₓ R₁] [Semiringₓ R₂] [CommSemiringₓ R₃] [CommSemiringₓ R₄] {σ₁₂ : R₁ →+* R₂}
  {σ₁₄ : R₁ →+* R₄} {σ₃₄ : R₃ →+* R₄} {M₁ M₂ M₃ M₄ : Type _} [TopologicalSpace M₁] [AddCommMonoidₓ M₁]
  [TopologicalSpace M₂] [AddCommMonoidₓ M₂] [TopologicalSpace M₃] [AddCommGroupₓ M₃] [TopologicalSpace M₄]
  [AddCommGroupₓ M₄]

theorem IsCompactOperator.smul {S : Type _} [Monoidₓ S] [DistribMulAction S M₂] [HasContinuousConstSmul S M₂]
    {f : M₁ → M₂} (hf : IsCompactOperator f) (c : S) : IsCompactOperator (c • f) :=
  let ⟨K, hK, hKf⟩ := hf
  ⟨c • K, hK.Image <| continuous_id.const_smul c, mem_of_superset hKf fun x hx => smul_mem_smul_set hx⟩

theorem IsCompactOperator.add [HasContinuousAdd M₂] {f g : M₁ → M₂} (hf : IsCompactOperator f)
    (hg : IsCompactOperator g) : IsCompactOperator (f + g) :=
  let ⟨A, hA, hAf⟩ := hf
  let ⟨B, hB, hBg⟩ := hg
  ⟨A + B, hA.add hB, mem_of_superset (inter_mem hAf hBg) fun x ⟨hxA, hxB⟩ => Set.add_mem_add hxA hxB⟩

theorem IsCompactOperator.neg [HasContinuousNeg M₄] {f : M₁ → M₄} (hf : IsCompactOperator f) : IsCompactOperator (-f) :=
  let ⟨K, hK, hKf⟩ := hf
  ⟨-K, hK.neg, (mem_of_superset hKf) fun x (hx : f x ∈ K) => Set.neg_mem_neg.mpr hx⟩

theorem IsCompactOperator.sub [TopologicalAddGroup M₄] {f g : M₁ → M₄} (hf : IsCompactOperator f)
    (hg : IsCompactOperator g) : IsCompactOperator (f - g) := by
  rw [sub_eq_add_neg] <;> exact hf.add hg.neg

variable (σ₁₄ M₁ M₄)

/-- The submodule of compact continuous linear maps. -/
def compactOperator [Module R₁ M₁] [Module R₄ M₄] [HasContinuousConstSmul R₄ M₄] [TopologicalAddGroup M₄] :
    Submodule R₄ (M₁ →SL[σ₁₄] M₄) where
  Carrier := { f | IsCompactOperator f }
  add_mem' := fun f g hf hg => hf.add hg
  zero_mem' := is_compact_operator_zero
  smul_mem' := fun c f hf => hf.smul c

end Operations

section Comp

variable {R₁ R₂ R₃ : Type _} [Semiringₓ R₁] [Semiringₓ R₂] [Semiringₓ R₃] {σ₁₂ : R₁ →+* R₂} {σ₂₃ : R₂ →+* R₃}
  {M₁ M₂ M₃ : Type _} [TopologicalSpace M₁] [TopologicalSpace M₂] [TopologicalSpace M₃] [AddCommMonoidₓ M₁]
  [Module R₁ M₁]

theorem IsCompactOperator.comp_clm [AddCommMonoidₓ M₂] [Module R₂ M₂] {f : M₂ → M₃} (hf : IsCompactOperator f)
    (g : M₁ →SL[σ₁₂] M₂) : IsCompactOperator (f ∘ g) := by
  have := g.continuous.tendsto 0
  rw [map_zero] at this
  rcases hf with ⟨K, hK, hKf⟩
  exact ⟨K, hK, this hKf⟩

theorem IsCompactOperator.continuous_comp {f : M₁ → M₂} (hf : IsCompactOperator f) {g : M₂ → M₃} (hg : Continuous g) :
    IsCompactOperator (g ∘ f) := by
  rcases hf with ⟨K, hK, hKf⟩
  refine' ⟨g '' K, hK.image hg, mem_of_superset hKf _⟩
  nth_rw 1[preimage_comp]
  exact preimage_mono (subset_preimage_image _ _)

theorem IsCompactOperator.clm_comp [AddCommMonoidₓ M₂] [Module R₂ M₂] [AddCommMonoidₓ M₃] [Module R₃ M₃] {f : M₁ → M₂}
    (hf : IsCompactOperator f) (g : M₂ →SL[σ₂₃] M₃) : IsCompactOperator (g ∘ f) :=
  hf.continuous_comp g.Continuous

end Comp

section CodRestrict

variable {R₁ R₂ : Type _} [Semiringₓ R₁] [Semiringₓ R₂] {σ₁₂ : R₁ →+* R₂} {M₁ M₂ : Type _} [TopologicalSpace M₁]
  [TopologicalSpace M₂] [AddCommMonoidₓ M₁] [AddCommMonoidₓ M₂] [Module R₁ M₁] [Module R₂ M₂]

theorem IsCompactOperator.cod_restrict {f : M₁ → M₂} (hf : IsCompactOperator f) {V : Submodule R₂ M₂}
    (hV : ∀ x, f x ∈ V) (h_closed : IsClosed (V : Set M₂)) : IsCompactOperator (Set.codRestrict f V hV) :=
  let ⟨K, hK, hKf⟩ := hf
  ⟨coe ⁻¹' K, (closed_embedding_subtype_coe h_closed).is_compact_preimage hK, hKf⟩

end CodRestrict

section Restrict

variable {R₁ R₂ R₃ : Type _} [Semiringₓ R₁] [Semiringₓ R₂] [Semiringₓ R₃] {σ₁₂ : R₁ →+* R₂} {σ₂₃ : R₂ →+* R₃}
  {M₁ M₂ M₃ : Type _} [TopologicalSpace M₁] [UniformSpace M₂] [TopologicalSpace M₃] [AddCommMonoidₓ M₁]
  [AddCommMonoidₓ M₂] [AddCommMonoidₓ M₃] [Module R₁ M₁] [Module R₂ M₂] [Module R₃ M₃]

/-- If a compact operator preserves a closed submodule, its restriction to that submodule is
compact.

Note that, following mathlib's convention in linear algebra, `restrict` designates the restriction
of an endomorphism `f : E →ₗ E` to an endomorphism `f' : ↥V →ₗ ↥V`. To prove that the restriction
`f' : ↥U →ₛₗ ↥V` of a compact operator `f : E →ₛₗ F` is compact, apply
`is_compact_operator.cod_restrict` to `f ∘ U.subtypeL`, which is compact by
`is_compact_operator.comp_clm`. -/
theorem IsCompactOperator.restrict {f : M₁ →ₗ[R₁] M₁} (hf : IsCompactOperator f) {V : Submodule R₁ M₁}
    (hV : ∀ v ∈ V, f v ∈ V) (h_closed : IsClosed (V : Set M₁)) : IsCompactOperator (f.restrict hV) :=
  (hf.comp_clm V.subtypeL).codRestrict (SetLike.forall.2 hV) h_closed

/-- If a compact operator preserves a complete submodule, its restriction to that submodule is
compact.

Note that, following mathlib's convention in linear algebra, `restrict` designates the restriction
of an endomorphism `f : E →ₗ E` to an endomorphism `f' : ↥V →ₗ ↥V`. To prove that the restriction
`f' : ↥U →ₛₗ ↥V` of a compact operator `f : E →ₛₗ F` is compact, apply
`is_compact_operator.cod_restrict` to `f ∘ U.subtypeL`, which is compact by
`is_compact_operator.comp_clm`. -/
theorem IsCompactOperator.restrict' [SeparatedSpace M₂] {f : M₂ →ₗ[R₂] M₂} (hf : IsCompactOperator f)
    {V : Submodule R₂ M₂} (hV : ∀ v ∈ V, f v ∈ V) [hcomplete : CompleteSpace V] : IsCompactOperator (f.restrict hV) :=
  hf.restrict hV (complete_space_coe_iff_is_complete.mp hcomplete).IsClosed

end Restrict

section Continuous

variable {𝕜₁ 𝕜₂ : Type _} [NontriviallyNormedField 𝕜₁] [NontriviallyNormedField 𝕜₂] {σ₁₂ : 𝕜₁ →+* 𝕜₂}
  [RingHomIsometric σ₁₂] {M₁ M₂ : Type _} [TopologicalSpace M₁] [AddCommGroupₓ M₁] [TopologicalSpace M₂]
  [AddCommGroupₓ M₂] [Module 𝕜₁ M₁] [Module 𝕜₂ M₂] [TopologicalAddGroup M₁] [HasContinuousConstSmul 𝕜₁ M₁]
  [TopologicalAddGroup M₂] [HasContinuousSmul 𝕜₂ M₂]

@[continuity]
theorem IsCompactOperator.continuous {f : M₁ →ₛₗ[σ₁₂] M₂} (hf : IsCompactOperator f) : Continuous f := by
  letI : UniformSpace M₂ := TopologicalAddGroup.toUniformSpace _
  haveI : UniformAddGroup M₂ := topological_add_comm_group_is_uniform
  -- Since `f` is linear, we only need to show that it is continuous at zero.
  -- Let `U` be a neighborhood of `0` in `M₂`.
  refine' continuous_of_continuous_at_zero f fun U hU => _
  rw [map_zero] at hU
  -- The compactness of `f` gives us a compact set `K : set M₂` such that `f ⁻¹' K` is a
  -- neighborhood of `0` in `M₁`.
  rcases hf with ⟨K, hK, hKf⟩
  -- But any compact set is totally bounded, hence Von-Neumann bounded. Thus, `K` absorbs `U`.
  -- This gives `r > 0` such that `∀ a : 𝕜₂, r ≤ ∥a∥ → K ⊆ a • U`.
  rcases hK.totally_bounded.is_vonN_bounded 𝕜₂ hU with ⟨r, hr, hrU⟩
  -- Choose `c : 𝕜₂` with `r < ∥c∥`.
  rcases NormedField.exists_lt_norm 𝕜₁ r with ⟨c, hc⟩
  have hcnz : c ≠ 0 := ne_zero_of_norm_ne_zero (hr.trans hc).Ne.symm
  -- We have `f ⁻¹' ((σ₁₂ c⁻¹) • K) = c⁻¹ • f ⁻¹' K ∈ 𝓝 0`. Thus, showing that
  -- `(σ₁₂ c⁻¹) • K ⊆ U` is enough to deduce that `f ⁻¹' U ∈ 𝓝 0`.
  suffices (σ₁₂ <| c⁻¹) • K ⊆ U by
    refine' mem_of_superset _ this
    have : IsUnit c⁻¹ := hcnz.is_unit.inv
    rwa [mem_map, preimage_smul_setₛₗ _ _ _ f this, set_smul_mem_nhds_zero_iff (inv_ne_zero hcnz)]
    infer_instance
  -- Since `σ₁₂ c⁻¹` = `(σ₁₂ c)⁻¹`, we have to prove that `K ⊆ σ₁₂ c • U`.
  rw [map_inv₀, ← subset_set_smul_iff₀ ((map_ne_zero σ₁₂).mpr hcnz)]
  -- But `σ₁₂` is isometric, so `∥σ₁₂ c∥ = ∥c∥ > r`, which concludes the argument since
  -- `∀ a : 𝕜₂, r ≤ ∥a∥ → K ⊆ a • U`.
  refine' hrU (σ₁₂ c) _
  rw [RingHomIsometric.is_iso]
  exact hc.le

/-- Upgrade a compact `linear_map` to a `continuous_linear_map`. -/
def ContinuousLinearMap.mkOfIsCompactOperator {f : M₁ →ₛₗ[σ₁₂] M₂} (hf : IsCompactOperator f) : M₁ →SL[σ₁₂] M₂ :=
  ⟨f, hf.Continuous⟩

@[simp]
theorem ContinuousLinearMap.mk_of_is_compact_operator_to_linear_map {f : M₁ →ₛₗ[σ₁₂] M₂} (hf : IsCompactOperator f) :
    (ContinuousLinearMap.mkOfIsCompactOperator hf : M₁ →ₛₗ[σ₁₂] M₂) = f :=
  rfl

@[simp]
theorem ContinuousLinearMap.coe_mk_of_is_compact_operator {f : M₁ →ₛₗ[σ₁₂] M₂} (hf : IsCompactOperator f) :
    (ContinuousLinearMap.mkOfIsCompactOperator hf : M₁ → M₂) = f :=
  rfl

theorem ContinuousLinearMap.mk_of_is_compact_operator_mem_compact_operator {f : M₁ →ₛₗ[σ₁₂] M₂}
    (hf : IsCompactOperator f) : ContinuousLinearMap.mkOfIsCompactOperator hf ∈ compactOperator σ₁₂ M₁ M₂ :=
  hf

end Continuous

theorem is_closed_set_of_is_compact_operator {𝕜₁ 𝕜₂ : Type _} [NontriviallyNormedField 𝕜₁] [NontriviallyNormedField 𝕜₂]
    {σ₁₂ : 𝕜₁ →+* 𝕜₂} [RingHomIsometric σ₁₂] {M₁ M₂ : Type _} [SeminormedAddCommGroup M₁] [NormedAddCommGroup M₂]
    [NormedSpace 𝕜₁ M₁] [NormedSpace 𝕜₂ M₂] [CompleteSpace M₂] :
    IsClosed { f : M₁ →SL[σ₁₂] M₂ | IsCompactOperator f } := by
  refine' is_closed_of_closure_subset _
  rintro u hu
  rw [Metric.mem_closure_iff] at hu
  suffices TotallyBounded (u '' Metric.ClosedBall 0 1) by
    change IsCompactOperator (u : M₁ →ₛₗ[σ₁₂] M₂)
    rw [is_compact_operator_iff_is_compact_closure_image_closed_ball (u : M₁ →ₛₗ[σ₁₂] M₂) zero_lt_one]
    exact compact_of_totally_bounded_is_closed this.closure is_closed_closure
  rw [Metric.totally_bounded_iff]
  intro ε hε
  rcases hu (ε / 2)
      (by
        linarith) with
    ⟨v, hv, huv⟩
  rcases(hv.is_compact_closure_image_closed_ball 1).finite_cover_balls
      (show 0 < ε / 2 by
        linarith) with
    ⟨T, -, hT, hTv⟩
  have hTv : v '' closed_ball 0 1 ⊆ _ := subset_closure.trans hTv
  refine' ⟨T, hT, _⟩
  rw [image_subset_iff] at hTv⊢
  intro x hx
  specialize hTv hx
  rw [mem_preimage, mem_Union₂] at hTv⊢
  rcases hTv with ⟨t, ht, htx⟩
  refine' ⟨t, ht, _⟩
  suffices dist (u x) (v x) < ε / 2 by
    rw [mem_ball] at *
    linarith [dist_triangle (u x) (v x) t]
  rw [mem_closed_ball_zero_iff] at hx
  calc
    dist (u x) (v x) = ∥u x - v x∥ := dist_eq_norm _ _
    _ = ∥(u - v) x∥ := by
      rw [ContinuousLinearMap.sub_apply] <;> rfl
    _ ≤ ∥u - v∥ := (u - v).unit_le_op_norm x hx
    _ = dist u v := (dist_eq_norm _ _).symm
    _ < ε / 2 := huv
    

theorem compact_operator_topological_closure {𝕜₁ 𝕜₂ : Type _} [NontriviallyNormedField 𝕜₁] [NontriviallyNormedField 𝕜₂]
    {σ₁₂ : 𝕜₁ →+* 𝕜₂} [RingHomIsometric σ₁₂] {M₁ M₂ : Type _} [SeminormedAddCommGroup M₁] [NormedAddCommGroup M₂]
    [NormedSpace 𝕜₁ M₁] [NormedSpace 𝕜₂ M₂] [CompleteSpace M₂] :
    (compactOperator σ₁₂ M₁ M₂).topologicalClosure = compactOperator σ₁₂ M₁ M₂ :=
  SetLike.ext' is_closed_set_of_is_compact_operator.closure_eq

theorem is_compact_operator_of_tendsto {ι 𝕜₁ 𝕜₂ : Type _} [NontriviallyNormedField 𝕜₁] [NontriviallyNormedField 𝕜₂]
    {σ₁₂ : 𝕜₁ →+* 𝕜₂} [RingHomIsometric σ₁₂] {M₁ M₂ : Type _} [SeminormedAddCommGroup M₁] [NormedAddCommGroup M₂]
    [NormedSpace 𝕜₁ M₁] [NormedSpace 𝕜₂ M₂] [CompleteSpace M₂] {l : Filter ι} [l.ne_bot] {F : ι → M₁ →SL[σ₁₂] M₂}
    {f : M₁ →SL[σ₁₂] M₂} (hf : Tendsto F l (𝓝 f)) (hF : ∀ᶠ i in l, IsCompactOperator (F i)) : IsCompactOperator f :=
  is_closed_set_of_is_compact_operator.mem_of_tendsto hf hF

