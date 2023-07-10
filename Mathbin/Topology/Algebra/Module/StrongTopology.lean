/-
Copyright (c) 2022 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker

! This file was ported from Lean 3 source module topology.algebra.module.strong_topology
! leanprover-community/mathlib commit 8905e5ed90859939681a725b00f6063e65096d95
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Topology.Algebra.UniformConvergence

/-!
# Strong topologies on the space of continuous linear maps

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In this file, we define the strong topologies on `E →L[𝕜] F` associated with a family
`𝔖 : set (set E)` to be the topology of uniform convergence on the elements of `𝔖` (also called
the topology of `𝔖`-convergence).

The lemma `uniform_on_fun.has_continuous_smul_of_image_bounded` tells us that this is a
vector space topology if the continuous linear image of any element of `𝔖` is bounded (in the sense
of `bornology.is_vonN_bounded`).

We then declare an instance for the case where `𝔖` is exactly the set of all bounded subsets of
`E`, giving us the so-called "topology of uniform convergence on bounded sets" (or "topology of
bounded convergence"), which coincides with the operator norm topology in the case of
`normed_space`s.

Other useful examples include the weak-* topology (when `𝔖` is the set of finite sets or the set
of singletons) and the topology of compact convergence (when `𝔖` is the set of relatively compact
sets).

## Main definitions

* `continuous_linear_map.strong_topology` is the topology mentioned above for an arbitrary `𝔖`.
* `continuous_linear_map.topological_space` is the topology of bounded convergence. This is
  declared as an instance.

## Main statements

* `continuous_linear_map.strong_topology.topological_add_group` and
  `continuous_linear_map.strong_topology.has_continuous_smul` show that the strong topology
  makes `E →L[𝕜] F` a topological vector space, with the assumptions on `𝔖` mentioned above.
* `continuous_linear_map.topological_add_group` and
  `continuous_linear_map.has_continuous_smul` register these facts as instances for the special
  case of bounded convergence.

## References

* [N. Bourbaki, *Topological Vector Spaces*][bourbaki1987]

## TODO

* add a type alias for continuous linear maps with the topology of `𝔖`-convergence?

## Tags

uniform convergence, bounded convergence
-/


open scoped Topology UniformConvergence

namespace ContinuousLinearMap

section General

variable {𝕜₁ 𝕜₂ : Type _} [NormedField 𝕜₁] [NormedField 𝕜₂] (σ : 𝕜₁ →+* 𝕜₂) {E E' F F' : Type _}
  [AddCommGroup E] [Module 𝕜₁ E] [AddCommGroup E'] [Module ℝ E'] [AddCommGroup F] [Module 𝕜₂ F]
  [AddCommGroup F'] [Module ℝ F'] [TopologicalSpace E] [TopologicalSpace E'] (F)

#print ContinuousLinearMap.strongTopology /-
/-- Given `E` and `F` two topological vector spaces and `𝔖 : set (set E)`, then
`strong_topology σ F 𝔖` is the "topology of uniform convergence on the elements of `𝔖`" on
`E →L[𝕜] F`.

If the continuous linear image of any element of `𝔖` is bounded, this makes `E →L[𝕜] F` a
topological vector space. -/
def strongTopology [TopologicalSpace F] [TopologicalAddGroup F] (𝔖 : Set (Set E)) :
    TopologicalSpace (E →SL[σ] F) :=
  (@UniformOnFun.topologicalSpace E F (TopologicalAddGroup.toUniformSpace F) 𝔖).induced coeFn
#align continuous_linear_map.strong_topology ContinuousLinearMap.strongTopology
-/

#print ContinuousLinearMap.strongUniformity /-
/-- The uniform structure associated with `continuous_linear_map.strong_topology`. We make sure
that this has nice definitional properties. -/
def strongUniformity [UniformSpace F] [UniformAddGroup F] (𝔖 : Set (Set E)) :
    UniformSpace (E →SL[σ] F) :=
  @UniformSpace.replaceTopology _ (strongTopology σ F 𝔖)
    ((UniformOnFun.uniformSpace E F 𝔖).comap coeFn)
    (by rw [strong_topology, UniformAddGroup.toUniformSpace_eq] <;> rfl)
#align continuous_linear_map.strong_uniformity ContinuousLinearMap.strongUniformity
-/

#print ContinuousLinearMap.strongUniformity_topology_eq /-
@[simp]
theorem strongUniformity_topology_eq [UniformSpace F] [UniformAddGroup F] (𝔖 : Set (Set E)) :
    (strongUniformity σ F 𝔖).toTopologicalSpace = strongTopology σ F 𝔖 :=
  rfl
#align continuous_linear_map.strong_uniformity_topology_eq ContinuousLinearMap.strongUniformity_topology_eq
-/

#print ContinuousLinearMap.strongUniformity.uniformEmbedding_coeFn /-
theorem strongUniformity.uniformEmbedding_coeFn [UniformSpace F] [UniformAddGroup F]
    (𝔖 : Set (Set E)) :
    @UniformEmbedding (E →SL[σ] F) (E →ᵤ[𝔖] F) (strongUniformity σ F 𝔖)
      (UniformOnFun.uniformSpace E F 𝔖) coeFn :=
  letI : UniformSpace (E →SL[σ] F) := strong_uniformity σ F 𝔖
  ⟨⟨rfl⟩, FunLike.coe_injective⟩
#align continuous_linear_map.strong_uniformity.uniform_embedding_coe_fn ContinuousLinearMap.strongUniformity.uniformEmbedding_coeFn
-/

#print ContinuousLinearMap.strongTopology.embedding_coeFn /-
theorem strongTopology.embedding_coeFn [UniformSpace F] [UniformAddGroup F] (𝔖 : Set (Set E)) :
    @Embedding (E →SL[σ] F) (E →ᵤ[𝔖] F) (strongTopology σ F 𝔖) (UniformOnFun.topologicalSpace E F 𝔖)
      (UniformOnFun.ofFun 𝔖 ∘ coeFn) :=
  @UniformEmbedding.embedding _ _ (id _) _ _ (strongUniformity.uniformEmbedding_coeFn _ _ _)
#align continuous_linear_map.strong_topology.embedding_coe_fn ContinuousLinearMap.strongTopology.embedding_coeFn
-/

#print ContinuousLinearMap.strongUniformity.uniformAddGroup /-
theorem strongUniformity.uniformAddGroup [UniformSpace F] [UniformAddGroup F] (𝔖 : Set (Set E)) :
    @UniformAddGroup (E →SL[σ] F) (strongUniformity σ F 𝔖) _ :=
  by
  letI : UniformSpace (E →SL[σ] F) := strong_uniformity σ F 𝔖
  rw [strong_uniformity, UniformSpace.replaceTopology_eq]
  let φ : (E →SL[σ] F) →+ E →ᵤ[𝔖] F := ⟨(coeFn : (E →SL[σ] F) → E →ᵤ F), rfl, fun _ _ => rfl⟩
  exact uniformAddGroup_comap φ
#align continuous_linear_map.strong_uniformity.uniform_add_group ContinuousLinearMap.strongUniformity.uniformAddGroup
-/

#print ContinuousLinearMap.strongTopology.topologicalAddGroup /-
theorem strongTopology.topologicalAddGroup [TopologicalSpace F] [TopologicalAddGroup F]
    (𝔖 : Set (Set E)) : @TopologicalAddGroup (E →SL[σ] F) (strongTopology σ F 𝔖) _ :=
  by
  letI : UniformSpace F := TopologicalAddGroup.toUniformSpace F
  haveI : UniformAddGroup F := comm_topologicalAddGroup_is_uniform
  letI : UniformSpace (E →SL[σ] F) := strong_uniformity σ F 𝔖
  haveI : UniformAddGroup (E →SL[σ] F) := strong_uniformity.uniform_add_group σ F 𝔖
  infer_instance
#align continuous_linear_map.strong_topology.topological_add_group ContinuousLinearMap.strongTopology.topologicalAddGroup
-/

#print ContinuousLinearMap.strongTopology.t2Space /-
theorem strongTopology.t2Space [TopologicalSpace F] [TopologicalAddGroup F] [T2Space F]
    (𝔖 : Set (Set E)) (h𝔖 : ⋃₀ 𝔖 = Set.univ) : @T2Space (E →SL[σ] F) (strongTopology σ F 𝔖) :=
  by
  letI : UniformSpace F := TopologicalAddGroup.toUniformSpace F
  haveI : UniformAddGroup F := comm_topologicalAddGroup_is_uniform
  letI : TopologicalSpace (E →SL[σ] F) := strong_topology σ F 𝔖
  haveI : T2Space (E →ᵤ[𝔖] F) := UniformOnFun.t2Space_of_covering h𝔖
  exact (strong_topology.embedding_coe_fn σ F 𝔖).T2Space
#align continuous_linear_map.strong_topology.t2_space ContinuousLinearMap.strongTopology.t2Space
-/

#print ContinuousLinearMap.strongTopology.continuousSMul /-
theorem strongTopology.continuousSMul [RingHomSurjective σ] [RingHomIsometric σ]
    [TopologicalSpace F] [TopologicalAddGroup F] [ContinuousSMul 𝕜₂ F] (𝔖 : Set (Set E))
    (h𝔖₁ : 𝔖.Nonempty) (h𝔖₂ : DirectedOn (· ⊆ ·) 𝔖) (h𝔖₃ : ∀ S ∈ 𝔖, Bornology.IsVonNBounded 𝕜₁ S) :
    @ContinuousSMul 𝕜₂ (E →SL[σ] F) _ _ (strongTopology σ F 𝔖) :=
  by
  letI : UniformSpace F := TopologicalAddGroup.toUniformSpace F
  haveI : UniformAddGroup F := comm_topologicalAddGroup_is_uniform
  letI : TopologicalSpace (E →SL[σ] F) := strong_topology σ F 𝔖
  let φ : (E →SL[σ] F) →ₗ[𝕜₂] E →ᵤ[𝔖] F :=
    ⟨(coeFn : (E →SL[σ] F) → E → F), fun _ _ => rfl, fun _ _ => rfl⟩
  exact
    UniformOnFun.continuousSMul_induced_of_image_bounded 𝕜₂ E F (E →SL[σ] F) h𝔖₁ h𝔖₂ φ ⟨rfl⟩
      fun u s hs => (h𝔖₃ s hs).image u
#align continuous_linear_map.strong_topology.has_continuous_smul ContinuousLinearMap.strongTopology.continuousSMul
-/

#print ContinuousLinearMap.strongTopology.hasBasis_nhds_zero_of_basis /-
theorem strongTopology.hasBasis_nhds_zero_of_basis [TopologicalSpace F] [TopologicalAddGroup F]
    {ι : Type _} (𝔖 : Set (Set E)) (h𝔖₁ : 𝔖.Nonempty) (h𝔖₂ : DirectedOn (· ⊆ ·) 𝔖) {p : ι → Prop}
    {b : ι → Set F} (h : (𝓝 0 : Filter F).HasBasis p b) :
    (@nhds (E →SL[σ] F) (strongTopology σ F 𝔖) 0).HasBasis (fun Si : Set E × ι => Si.1 ∈ 𝔖 ∧ p Si.2)
      fun Si => {f : E →SL[σ] F | ∀ x ∈ Si.1, f x ∈ b Si.2} :=
  by
  letI : UniformSpace F := TopologicalAddGroup.toUniformSpace F
  haveI : UniformAddGroup F := comm_topologicalAddGroup_is_uniform
  rw [nhds_induced]
  exact (UniformOnFun.hasBasis_nhds_zero_of_basis 𝔖 h𝔖₁ h𝔖₂ h).comap coeFn
#align continuous_linear_map.strong_topology.has_basis_nhds_zero_of_basis ContinuousLinearMap.strongTopology.hasBasis_nhds_zero_of_basis
-/

#print ContinuousLinearMap.strongTopology.hasBasis_nhds_zero /-
theorem strongTopology.hasBasis_nhds_zero [TopologicalSpace F] [TopologicalAddGroup F]
    (𝔖 : Set (Set E)) (h𝔖₁ : 𝔖.Nonempty) (h𝔖₂ : DirectedOn (· ⊆ ·) 𝔖) :
    (@nhds (E →SL[σ] F) (strongTopology σ F 𝔖) 0).HasBasis
      (fun SV : Set E × Set F => SV.1 ∈ 𝔖 ∧ SV.2 ∈ (𝓝 0 : Filter F)) fun SV =>
      {f : E →SL[σ] F | ∀ x ∈ SV.1, f x ∈ SV.2} :=
  strongTopology.hasBasis_nhds_zero_of_basis σ F 𝔖 h𝔖₁ h𝔖₂ (𝓝 0).basis_sets
#align continuous_linear_map.strong_topology.has_basis_nhds_zero ContinuousLinearMap.strongTopology.hasBasis_nhds_zero
-/

end General

section BoundedSets

variable {𝕜₁ 𝕜₂ 𝕜₃ : Type _} [NormedField 𝕜₁] [NormedField 𝕜₂] [NormedField 𝕜₃] {σ : 𝕜₁ →+* 𝕜₂}
  {τ : 𝕜₂ →+* 𝕜₃} {ρ : 𝕜₁ →+* 𝕜₃} [RingHomCompTriple σ τ ρ] {E E' F F' G : Type _} [AddCommGroup E]
  [Module 𝕜₁ E] [AddCommGroup E'] [Module ℝ E'] [AddCommGroup F] [Module 𝕜₂ F] [AddCommGroup F']
  [Module ℝ F'] [AddCommGroup G] [Module 𝕜₃ G] [TopologicalSpace E]

/-- The topology of bounded convergence on `E →L[𝕜] F`. This coincides with the topology induced by
the operator norm when `E` and `F` are normed spaces. -/
instance [TopologicalSpace F] [TopologicalAddGroup F] : TopologicalSpace (E →SL[σ] F) :=
  strongTopology σ F {S | Bornology.IsVonNBounded 𝕜₁ S}

instance [TopologicalSpace F] [TopologicalAddGroup F] : TopologicalAddGroup (E →SL[σ] F) :=
  strongTopology.topologicalAddGroup σ F _

instance [RingHomSurjective σ] [RingHomIsometric σ] [TopologicalSpace F] [TopologicalAddGroup F]
    [ContinuousSMul 𝕜₂ F] : ContinuousSMul 𝕜₂ (E →SL[σ] F) :=
  strongTopology.continuousSMul σ F {S | Bornology.IsVonNBounded 𝕜₁ S}
    ⟨∅, Bornology.isVonNBounded_empty 𝕜₁ E⟩
    (directedOn_of_sup_mem fun _ _ => Bornology.IsVonNBounded.union) fun s hs => hs

instance [UniformSpace F] [UniformAddGroup F] : UniformSpace (E →SL[σ] F) :=
  strongUniformity σ F {S | Bornology.IsVonNBounded 𝕜₁ S}

instance [UniformSpace F] [UniformAddGroup F] : UniformAddGroup (E →SL[σ] F) :=
  strongUniformity.uniformAddGroup σ F _

instance [TopologicalSpace F] [TopologicalAddGroup F] [ContinuousSMul 𝕜₁ E] [T2Space F] :
    T2Space (E →SL[σ] F) :=
  strongTopology.t2Space σ F _
    (Set.eq_univ_of_forall fun x =>
      Set.mem_sUnion_of_mem (Set.mem_singleton x) (Bornology.isVonNBounded_singleton x))

#print ContinuousLinearMap.hasBasis_nhds_zero_of_basis /-
protected theorem hasBasis_nhds_zero_of_basis [TopologicalSpace F] [TopologicalAddGroup F]
    {ι : Type _} {p : ι → Prop} {b : ι → Set F} (h : (𝓝 0 : Filter F).HasBasis p b) :
    (𝓝 (0 : E →SL[σ] F)).HasBasis (fun Si : Set E × ι => Bornology.IsVonNBounded 𝕜₁ Si.1 ∧ p Si.2)
      fun Si => {f : E →SL[σ] F | ∀ x ∈ Si.1, f x ∈ b Si.2} :=
  strongTopology.hasBasis_nhds_zero_of_basis σ F {S | Bornology.IsVonNBounded 𝕜₁ S}
    ⟨∅, Bornology.isVonNBounded_empty 𝕜₁ E⟩
    (directedOn_of_sup_mem fun _ _ => Bornology.IsVonNBounded.union) h
#align continuous_linear_map.has_basis_nhds_zero_of_basis ContinuousLinearMap.hasBasis_nhds_zero_of_basis
-/

#print ContinuousLinearMap.hasBasis_nhds_zero /-
protected theorem hasBasis_nhds_zero [TopologicalSpace F] [TopologicalAddGroup F] :
    (𝓝 (0 : E →SL[σ] F)).HasBasis
      (fun SV : Set E × Set F => Bornology.IsVonNBounded 𝕜₁ SV.1 ∧ SV.2 ∈ (𝓝 0 : Filter F))
      fun SV => {f : E →SL[σ] F | ∀ x ∈ SV.1, f x ∈ SV.2} :=
  ContinuousLinearMap.hasBasis_nhds_zero_of_basis (𝓝 0).basis_sets
#align continuous_linear_map.has_basis_nhds_zero ContinuousLinearMap.hasBasis_nhds_zero
-/

variable (G) [TopologicalSpace F] [TopologicalSpace G]

#print ContinuousLinearMap.precomp /-
/-- Pre-composition by a *fixed* continuous linear map as a continuous linear map.
Note that in non-normed space it is not always true that composition is continuous
in both variables, so we have to fix one of them. -/
@[simps]
def precomp [TopologicalAddGroup G] [ContinuousConstSMul 𝕜₃ G] [RingHomSurjective σ]
    [RingHomIsometric σ] (L : E →SL[σ] F) : (F →SL[τ] G) →L[𝕜₃] E →SL[ρ] G
    where
  toFun f := f.comp L
  map_add' f g := add_comp f g L
  map_smul' a f := smul_comp a f L
  cont := by
    letI : UniformSpace G := TopologicalAddGroup.toUniformSpace G
    haveI : UniformAddGroup G := comm_topologicalAddGroup_is_uniform
    rw [(strong_topology.embedding_coe_fn _ _ _).continuous_iff]
    refine'
      (UniformOnFun.precomp_uniformContinuous _).Continuous.comp
        (strong_topology.embedding_coe_fn _ _ _).Continuous
    exact fun S hS => hS.image L
#align continuous_linear_map.precomp ContinuousLinearMap.precomp
-/

variable (E) {G}

#print ContinuousLinearMap.postcomp /-
/-- Post-composition by a *fixed* continuous linear map as a continuous linear map.
Note that in non-normed space it is not always true that composition is continuous
in both variables, so we have to fix one of them. -/
@[simps]
def postcomp [TopologicalAddGroup F] [TopologicalAddGroup G] [ContinuousConstSMul 𝕜₃ G]
    [ContinuousConstSMul 𝕜₂ F] (L : F →SL[τ] G) : (E →SL[σ] F) →SL[τ] E →SL[ρ] G
    where
  toFun f := L.comp f
  map_add' := comp_add L
  map_smul' := comp_smulₛₗ L
  cont := by
    letI : UniformSpace G := TopologicalAddGroup.toUniformSpace G
    haveI : UniformAddGroup G := comm_topologicalAddGroup_is_uniform
    letI : UniformSpace F := TopologicalAddGroup.toUniformSpace F
    haveI : UniformAddGroup F := comm_topologicalAddGroup_is_uniform
    rw [(strong_topology.embedding_coe_fn _ _ _).continuous_iff]
    exact
      (UniformOnFun.postcomp_uniformContinuous L.uniform_continuous).Continuous.comp
        (strong_topology.embedding_coe_fn _ _ _).Continuous
#align continuous_linear_map.postcomp ContinuousLinearMap.postcomp
-/

end BoundedSets

end ContinuousLinearMap

open ContinuousLinearMap

namespace ContinuousLinearEquiv

section Semilinear

variable {𝕜 : Type _} {𝕜₂ : Type _} {𝕜₃ : Type _} {𝕜₄ : Type _} {E : Type _} {F : Type _}
  {G : Type _} {H : Type _} [AddCommGroup E] [AddCommGroup F] [AddCommGroup G] [AddCommGroup H]
  [NontriviallyNormedField 𝕜] [NontriviallyNormedField 𝕜₂] [NontriviallyNormedField 𝕜₃]
  [NontriviallyNormedField 𝕜₄] [Module 𝕜 E] [Module 𝕜₂ F] [Module 𝕜₃ G] [Module 𝕜₄ H]
  [TopologicalSpace E] [TopologicalSpace F] [TopologicalSpace G] [TopologicalSpace H]
  [TopologicalAddGroup G] [TopologicalAddGroup H] [ContinuousConstSMul 𝕜₃ G]
  [ContinuousConstSMul 𝕜₄ H] {σ₁₂ : 𝕜 →+* 𝕜₂} {σ₂₁ : 𝕜₂ →+* 𝕜} {σ₂₃ : 𝕜₂ →+* 𝕜₃} {σ₁₃ : 𝕜 →+* 𝕜₃}
  {σ₃₄ : 𝕜₃ →+* 𝕜₄} {σ₄₃ : 𝕜₄ →+* 𝕜₃} {σ₂₄ : 𝕜₂ →+* 𝕜₄} {σ₁₄ : 𝕜 →+* 𝕜₄} [RingHomInvPair σ₁₂ σ₂₁]
  [RingHomInvPair σ₂₁ σ₁₂] [RingHomInvPair σ₃₄ σ₄₃] [RingHomInvPair σ₄₃ σ₃₄]
  [RingHomCompTriple σ₂₁ σ₁₄ σ₂₄] [RingHomCompTriple σ₂₄ σ₄₃ σ₂₃] [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃]
  [RingHomCompTriple σ₁₃ σ₃₄ σ₁₄] [RingHomCompTriple σ₂₃ σ₃₄ σ₂₄] [RingHomCompTriple σ₁₂ σ₂₄ σ₁₄]
  [RingHomIsometric σ₁₂] [RingHomIsometric σ₂₁]

#print ContinuousLinearEquiv.arrowCongrSL /-
/-- A pair of continuous (semi)linear equivalences generates a (semi)linear equivalence between the
spaces of continuous (semi)linear maps. -/
@[simps]
def arrowCongrSL (e₁₂ : E ≃SL[σ₁₂] F) (e₄₃ : H ≃SL[σ₄₃] G) : (E →SL[σ₁₄] H) ≃SL[σ₄₃] F →SL[σ₂₃] G :=
  {-- given explicitly to help `simps`
        -- given explicitly to help `simps`
        e₁₂.arrowCongrEquiv
      e₄₃ with
    toFun := fun L => (e₄₃ : H →SL[σ₄₃] G).comp (L.comp (e₁₂.symm : F →SL[σ₂₁] E))
    invFun := fun L => (e₄₃.symm : G →SL[σ₃₄] H).comp (L.comp (e₁₂ : E →SL[σ₁₂] F))
    map_add' := fun f g => by rw [add_comp, comp_add]
    map_smul' := fun t f => by rw [smul_comp, comp_smulₛₗ]
    continuous_toFun :=
      ((postcomp F e₄₃.toContinuousLinearMap).comp
          (precomp H e₁₂.symm.toContinuousLinearMap)).Continuous
    continuous_invFun :=
      ((precomp H e₁₂.toContinuousLinearMap).comp
          (postcomp F e₄₃.symm.toContinuousLinearMap)).Continuous }
#align continuous_linear_equiv.arrow_congrSL ContinuousLinearEquiv.arrowCongrSL
-/

end Semilinear

section Linear

variable {𝕜 : Type _} {E : Type _} {F : Type _} {G : Type _} {H : Type _} [AddCommGroup E]
  [AddCommGroup F] [AddCommGroup G] [AddCommGroup H] [NontriviallyNormedField 𝕜] [Module 𝕜 E]
  [Module 𝕜 F] [Module 𝕜 G] [Module 𝕜 H] [TopologicalSpace E] [TopologicalSpace F]
  [TopologicalSpace G] [TopologicalSpace H] [TopologicalAddGroup G] [TopologicalAddGroup H]
  [ContinuousConstSMul 𝕜 G] [ContinuousConstSMul 𝕜 H]

#print ContinuousLinearEquiv.arrowCongr /-
/-- A pair of continuous linear equivalences generates an continuous linear equivalence between
the spaces of continuous linear maps. -/
def arrowCongr (e₁ : E ≃L[𝕜] F) (e₂ : H ≃L[𝕜] G) : (E →L[𝕜] H) ≃L[𝕜] F →L[𝕜] G :=
  e₁.arrowCongrSL e₂
#align continuous_linear_equiv.arrow_congr ContinuousLinearEquiv.arrowCongr
-/

end Linear

end ContinuousLinearEquiv

