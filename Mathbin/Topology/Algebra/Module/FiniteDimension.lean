/-
Copyright (c) 2022 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Anatole Dedecker

! This file was ported from Lean 3 source module topology.algebra.module.finite_dimension
! leanprover-community/mathlib commit 46a64b5b4268c594af770c44d9e502afc6a515cb
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Analysis.LocallyConvex.BalancedCoreHull
import Mathbin.Topology.Algebra.Module.Determinant

/-!
# Finite dimensional topological vector spaces over complete fields

Let `𝕜` be a complete nontrivially normed field, and `E` a topological vector space (TVS) over
`𝕜` (i.e we have `[add_comm_group E] [module 𝕜 E] [topological_space E] [topological_add_group E]`
and `[has_continuous_smul 𝕜 E]`).

If `E` is finite dimensional and Hausdorff, then all linear maps from `E` to any other TVS are
continuous.

When `E` is a normed space, this gets us the equivalence of norms in finite dimension.

## Main results :

* `linear_map.continuous_iff_is_closed_ker` : a linear form is continuous if and only if its kernel
  is closed.
* `linear_map.continuous_of_finite_dimensional` : a linear map on a finite-dimensional Hausdorff
  space over a complete field is continuous.

## TODO

Generalize more of `analysis/normed_space/finite_dimension` to general TVSs.

## Implementation detail

The main result from which everything follows is the fact that, if `ξ : ι → E` is a finite basis,
then `ξ.equiv_fun : E →ₗ (ι → 𝕜)` is continuous. However, for technical reasons, it is easier to
prove this when `ι` and `E` live ine the same universe. So we start by doing that as a private
lemma, then we deduce `linear_map.continuous_of_finite_dimensional` from it, and then the general
result follows as `continuous_equiv_fun_basis`.

-/


universe u v w x

noncomputable section

open Set FiniteDimensional TopologicalSpace Filter

open BigOperators

section Semiring

variable {ι 𝕜 F : Type _} [Finite ι] [Semiring 𝕜] [TopologicalSpace 𝕜] [AddCommMonoid F]
  [Module 𝕜 F] [TopologicalSpace F] [HasContinuousAdd F] [HasContinuousSmul 𝕜 F]

/-- A linear map on `ι → 𝕜` (where `ι` is finite) is continuous -/
theorem LinearMap.continuous_on_pi (f : (ι → 𝕜) →ₗ[𝕜] F) : Continuous f :=
  by
  cases nonempty_fintype ι
  classical
    -- for the proof, write `f` in the standard basis, and use that each coordinate is a continuous
    -- function.
    have : (f : (ι → 𝕜) → F) = fun x => ∑ i : ι, x i • f fun j => if i = j then 1 else 0 :=
      by
      ext x
      exact f.pi_apply_eq_sum_univ x
    rw [this]
    refine' continuous_finset_sum _ fun i hi => _
    exact (continuous_apply i).smul continuous_const
#align linear_map.continuous_on_pi LinearMap.continuous_on_pi

end Semiring

section Field

variable {𝕜 E F : Type _} [Field 𝕜] [TopologicalSpace 𝕜] [AddCommGroup E] [Module 𝕜 E]
  [TopologicalSpace E] [AddCommGroup F] [Module 𝕜 F] [TopologicalSpace F] [TopologicalAddGroup F]
  [HasContinuousSmul 𝕜 F]

/-- The space of continuous linear maps between finite-dimensional spaces is finite-dimensional. -/
instance [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F] : FiniteDimensional 𝕜 (E →L[𝕜] F) :=
  FiniteDimensional.of_injective (ContinuousLinearMap.coeLm 𝕜 : (E →L[𝕜] F) →ₗ[𝕜] E →ₗ[𝕜] F)
    ContinuousLinearMap.coe_injective

end Field

section NormedField

variable {𝕜 : Type u} [hnorm : NontriviallyNormedField 𝕜] {E : Type v} [AddCommGroup E] [Module 𝕜 E]
  [TopologicalSpace E] [TopologicalAddGroup E] [HasContinuousSmul 𝕜 E] {F : Type w} [AddCommGroup F]
  [Module 𝕜 F] [TopologicalSpace F] [TopologicalAddGroup F] [HasContinuousSmul 𝕜 F] {F' : Type x}
  [AddCommGroup F'] [Module 𝕜 F'] [TopologicalSpace F'] [TopologicalAddGroup F']
  [HasContinuousSmul 𝕜 F']

include hnorm

/-- If `𝕜` is a nontrivially normed field, any T2 topology on `𝕜` which makes it a topological
vector space over itself (with the norm topology) is *equal* to the norm topology. -/
theorem unique_topology_of_t2 {t : TopologicalSpace 𝕜} (h₁ : @TopologicalAddGroup 𝕜 t _)
    (h₂ : @HasContinuousSmul 𝕜 𝕜 _ hnorm.toUniformSpace.toTopologicalSpace t) (h₃ : @T2Space 𝕜 t) :
    t = hnorm.toUniformSpace.toTopologicalSpace :=
  by
  -- Let `𝓣₀` denote the topology on `𝕜` induced by the norm, and `𝓣` be any T2 vector
  -- topology on `𝕜`. To show that `𝓣₀ = 𝓣`, it suffices to show that they have the same
  -- neighborhoods of 0.
  refine' TopologicalAddGroup.ext h₁ inferInstance (le_antisymm _ _)
  · -- To show `𝓣 ≤ 𝓣₀`, we have to show that closed balls are `𝓣`-neighborhoods of 0.
    rw [metric.nhds_basis_closed_ball.ge_iff]
    -- Let `ε > 0`. Since `𝕜` is nontrivially normed, we have `0 < ‖ξ₀‖ < ε` for some `ξ₀ : 𝕜`.
    intro ε hε
    rcases NormedField.exists_norm_lt 𝕜 hε with ⟨ξ₀, hξ₀, hξ₀ε⟩
    -- Since `ξ₀ ≠ 0` and `𝓣` is T2, we know that `{ξ₀}ᶜ` is a `𝓣`-neighborhood of 0.
    have : {ξ₀}ᶜ ∈ @nhds 𝕜 t 0 :=
      IsOpen.mem_nhds is_open_compl_singleton (Ne.symm <| norm_ne_zero_iff.mp hξ₀.ne.symm)
    -- Thus, its balanced core `𝓑` is too. Let's show that the closed ball of radius `ε` contains
    -- `𝓑`, which will imply that the closed ball is indeed a `𝓣`-neighborhood of 0.
    have : balancedCore 𝕜 ({ξ₀}ᶜ) ∈ @nhds 𝕜 t 0 := balanced_core_mem_nhds_zero this
    refine' mem_of_superset this fun ξ hξ => _
    -- Let `ξ ∈ 𝓑`. We want to show `‖ξ‖ < ε`. If `ξ = 0`, this is trivial.
    by_cases hξ0 : ξ = 0
    · rw [hξ0]
      exact Metric.mem_closed_ball_self hε.le
    · rw [mem_closed_ball_zero_iff]
      -- Now suppose `ξ ≠ 0`. By contradiction, let's assume `ε < ‖ξ‖`, and show that
      -- `ξ₀ ∈ 𝓑 ⊆ {ξ₀}ᶜ`, which is a contradiction.
      by_contra' h
      suffices (ξ₀ * ξ⁻¹) • ξ ∈ balancedCore 𝕜 ({ξ₀}ᶜ)
        by
        rw [smul_eq_mul 𝕜, mul_assoc, inv_mul_cancel hξ0, mul_one] at this
        exact not_mem_compl_iff.mpr (mem_singleton ξ₀) ((balanced_core_subset _) this)
      -- For that, we use that `𝓑` is balanced : since `‖ξ₀‖ < ε < ‖ξ‖`, we have `‖ξ₀ / ξ‖ ≤ 1`,
      -- hence `ξ₀ = (ξ₀ / ξ) • ξ ∈ 𝓑` because `ξ ∈ 𝓑`.
      refine' (balancedCoreBalanced _).smul_mem _ hξ
      rw [norm_mul, norm_inv, mul_inv_le_iff (norm_pos_iff.mpr hξ0), mul_one]
      exact (hξ₀ε.trans h).le
  ·-- Finally, to show `𝓣₀ ≤ 𝓣`, we simply argue that `id = (λ x, x • 1)` is continuous from
    -- `(𝕜, 𝓣₀)` to `(𝕜, 𝓣)` because `(•) : (𝕜, 𝓣₀) × (𝕜, 𝓣) → (𝕜, 𝓣)` is continuous.
    calc
      @nhds 𝕜 hnorm.to_uniform_space.to_topological_space 0 =
          map id (@nhds 𝕜 hnorm.to_uniform_space.to_topological_space 0) :=
        map_id.symm
      _ = map (fun x => id x • 1) (@nhds 𝕜 hnorm.to_uniform_space.to_topological_space 0) := by
        conv_rhs =>
            congr
            ext
            rw [smul_eq_mul, mul_one] <;>
          rfl
      _ ≤ @nhds 𝕜 t ((0 : 𝕜) • 1) :=
        @tendsto.smul_const _ _ _ hnorm.to_uniform_space.to_topological_space t _ _ _ _ _ tendsto_id
          (1 : 𝕜)
      _ = @nhds 𝕜 t 0 := by rw [zero_smul]
      
#align unique_topology_of_t2 unique_topology_of_t2

/-- Any linear form on a topological vector space over a nontrivially normed field is continuous if
    its kernel is closed. -/
theorem LinearMap.continuous_of_is_closed_ker (l : E →ₗ[𝕜] 𝕜) (hl : IsClosed (l.ker : Set E)) :
    Continuous l :=
  by
  -- `l` is either constant or surjective. If it is constant, the result is trivial.
  by_cases H : finrank 𝕜 l.range = 0
  · rw [finrank_eq_zero, LinearMap.range_eq_bot] at H
    rw [H]
    exact continuous_zero
  · -- In the case where `l` is surjective, we factor it as `φ : (E ⧸ l.ker) ≃ₗ[𝕜] 𝕜`. Note that
    -- `E ⧸ l.ker` is T2 since `l.ker` is closed.
    have : finrank 𝕜 l.range = 1 :=
      le_antisymm (finrank_self 𝕜 ▸ l.range.finrank_le) (zero_lt_iff.mpr H)
    have hi : Function.Injective (l.ker.liftq l (le_refl _)) :=
      by
      rw [← LinearMap.ker_eq_bot]
      exact Submodule.ker_liftq_eq_bot _ _ _ (le_refl _)
    have hs : Function.Surjective (l.ker.liftq l (le_refl _)) :=
      by
      rw [← LinearMap.range_eq_top, Submodule.range_liftq]
      exact eq_top_of_finrank_eq ((finrank_self 𝕜).symm ▸ this)
    let φ : (E ⧸ l.ker) ≃ₗ[𝕜] 𝕜 := LinearEquiv.ofBijective (l.ker.liftq l (le_refl _)) ⟨hi, hs⟩
    have hlφ : (l : E → 𝕜) = φ ∘ l.ker.mkq := by ext <;> rfl
    -- Since the quotient map `E →ₗ[𝕜] (E ⧸ l.ker)` is continuous, the continuity of `l` will follow
    -- form the continuity of `φ`.
    suffices Continuous φ.to_equiv by
      rw [hlφ]
      exact this.comp continuous_quot_mk
    -- The pullback by `φ.symm` of the quotient topology is a T2 topology on `𝕜`, because `φ.symm`
    -- is injective. Since `φ.symm` is linear, it is also a vector space topology.
    -- Hence, we know that it is equal to the topology induced by the norm.
    have : induced φ.to_equiv.symm inferInstance = hnorm.to_uniform_space.to_topological_space :=
      by
      refine'
        unique_topology_of_t2 (topological_add_group_induced φ.symm.to_linear_map)
          (has_continuous_smul_induced φ.symm.to_linear_map) _
      rw [t2_space_iff]
      exact fun x y hxy =>
        @separated_by_continuous _ _ (induced _ _) _ _ _ continuous_induced_dom _ _
          (φ.to_equiv.symm.injective.ne hxy)
    -- Finally, the pullback by `φ.symm` is exactly the pushforward by `φ`, so we have to prove
    -- that `φ` is continuous when `𝕜` is endowed with the pushforward by `φ` of the quotient
    -- topology, which is trivial by definition of the pushforward.
    rw [this.symm, Equiv.induced_symm]
    exact continuous_coinduced_rng
#align linear_map.continuous_of_is_closed_ker LinearMap.continuous_of_is_closed_ker

/-- Any linear form on a topological vector space over a nontrivially normed field is continuous if
    and only if its kernel is closed. -/
theorem LinearMap.continuous_iff_is_closed_ker (l : E →ₗ[𝕜] 𝕜) :
    Continuous l ↔ IsClosed (l.ker : Set E) :=
  ⟨fun h => is_closed_singleton.Preimage h, l.continuous_of_is_closed_ker⟩
#align linear_map.continuous_iff_is_closed_ker LinearMap.continuous_iff_is_closed_ker

/-- Over a nontrivially normed field, any linear form which is nonzero on a nonempty open set is
    automatically continuous. -/
theorem LinearMap.continuous_of_nonzero_on_open (l : E →ₗ[𝕜] 𝕜) (s : Set E) (hs₁ : IsOpen s)
    (hs₂ : s.Nonempty) (hs₃ : ∀ x ∈ s, l x ≠ 0) : Continuous l :=
  by
  refine' l.continuous_of_is_closed_ker (l.is_closed_or_dense_ker.resolve_right fun hl => _)
  rcases hs₂ with ⟨x, hx⟩
  have : x ∈ interior ((l.ker : Set E)ᶜ) :=
    by
    rw [mem_interior_iff_mem_nhds]
    exact mem_of_superset (hs₁.mem_nhds hx) hs₃
  rwa [hl.interior_compl] at this
#align linear_map.continuous_of_nonzero_on_open LinearMap.continuous_of_nonzero_on_open

variable [CompleteSpace 𝕜]

/-- This version imposes `ι` and `E` to live in the same universe, so you should instead use
`continuous_equiv_fun_basis` which gives the same result without universe restrictions. -/
private theorem continuous_equiv_fun_basis_aux [ht2 : T2Space E] {ι : Type v} [Fintype ι]
    (ξ : Basis ι 𝕜 E) : Continuous ξ.equivFun :=
  by
  letI : UniformSpace E := TopologicalAddGroup.toUniformSpace E
  letI : UniformAddGroup E := topological_add_comm_group_is_uniform
  letI : SeparatedSpace E := separated_iff_t2.mpr ht2
  induction' hn : Fintype.card ι with n IH generalizing ι E
  · rw [Fintype.card_eq_zero_iff] at hn
    exact continuous_of_const fun x y => funext hn.elim
  · haveI : FiniteDimensional 𝕜 E := of_fintype_basis ξ
    -- first step: thanks to the induction hypothesis, any n-dimensional subspace is equivalent
    -- to a standard space of dimension n, hence it is complete and therefore closed.
    have H₁ : ∀ s : Submodule 𝕜 E, finrank 𝕜 s = n → IsClosed (s : Set E) :=
      by
      intro s s_dim
      letI : UniformAddGroup s := s.to_add_subgroup.uniform_add_group
      let b := Basis.ofVectorSpace 𝕜 s
      have U : UniformEmbedding b.equiv_fun.symm.to_equiv :=
        by
        have : Fintype.card (Basis.ofVectorSpaceIndex 𝕜 s) = n :=
          by
          rw [← s_dim]
          exact (finrank_eq_card_basis b).symm
        have : Continuous b.equiv_fun := IH b this
        exact
          b.equiv_fun.symm.uniform_embedding b.equiv_fun.symm.to_linear_map.continuous_on_pi this
      have : IsComplete (s : Set E) :=
        complete_space_coe_iff_is_complete.1 ((complete_space_congr U).1 (by infer_instance))
      exact this.is_closed
    -- second step: any linear form is continuous, as its kernel is closed by the first step
    have H₂ : ∀ f : E →ₗ[𝕜] 𝕜, Continuous f := by
      intro f
      by_cases H : finrank 𝕜 f.range = 0
      · rw [finrank_eq_zero, LinearMap.range_eq_bot] at H
        rw [H]
        exact continuous_zero
      · have : finrank 𝕜 f.ker = n :=
          by
          have Z := f.finrank_range_add_finrank_ker
          rw [finrank_eq_card_basis ξ, hn] at Z
          have : finrank 𝕜 f.range = 1 :=
            le_antisymm (finrank_self 𝕜 ▸ f.range.finrank_le) (zero_lt_iff.mpr H)
          rw [this, add_comm, Nat.add_one] at Z
          exact Nat.succ.inj Z
        have : IsClosed (f.ker : Set E) := H₁ _ this
        exact LinearMap.continuous_of_is_closed_ker f this
    rw [continuous_pi_iff]
    intro i
    change Continuous (ξ.coord i)
    exact H₂ (ξ.coord i)
#align continuous_equiv_fun_basis_aux continuous_equiv_fun_basis_aux

/-- Any linear map on a finite dimensional space over a complete field is continuous. -/
theorem LinearMap.continuous_of_finite_dimensional [T2Space E] [FiniteDimensional 𝕜 E]
    (f : E →ₗ[𝕜] F') : Continuous f :=
  by
  -- for the proof, go to a model vector space `b → 𝕜` thanks to `continuous_equiv_fun_basis`, and
  -- argue that all linear maps there are continuous.
  let b := Basis.ofVectorSpace 𝕜 E
  have A : Continuous b.equiv_fun := continuous_equiv_fun_basis_aux b
  have B : Continuous (f.comp (b.equiv_fun.symm : (Basis.ofVectorSpaceIndex 𝕜 E → 𝕜) →ₗ[𝕜] E)) :=
    LinearMap.continuous_on_pi _
  have :
    Continuous
      (f.comp (b.equiv_fun.symm : (Basis.ofVectorSpaceIndex 𝕜 E → 𝕜) →ₗ[𝕜] E) ∘ b.equiv_fun) :=
    B.comp A
  convert this
  ext x
  dsimp
  rw [Basis.equiv_fun_symm_apply, Basis.sum_repr]
#align linear_map.continuous_of_finite_dimensional LinearMap.continuous_of_finite_dimensional

instance LinearMap.continuousLinearMapClassOfFiniteDimensional [T2Space E] [FiniteDimensional 𝕜 E] :
    ContinuousLinearMapClass (E →ₗ[𝕜] F') 𝕜 E F' :=
  { LinearMap.semilinearMapClass with
    map_continuous := fun f => f.continuous_of_finite_dimensional }
#align
  linear_map.continuous_linear_map_class_of_finite_dimensional LinearMap.continuousLinearMapClassOfFiniteDimensional

/-- In finite dimensions over a non-discrete complete normed field, the canonical identification
(in terms of a basis) with `𝕜^n` (endowed with the product topology) is continuous.
This is the key fact wich makes all linear maps from a T2 finite dimensional TVS over such a field
continuous (see `linear_map.continuous_of_finite_dimensional`), which in turn implies that all
norms are equivalent in finite dimensions. -/
theorem continuous_equiv_fun_basis [T2Space E] {ι : Type _} [Fintype ι] (ξ : Basis ι 𝕜 E) :
    Continuous ξ.equivFun :=
  haveI : FiniteDimensional 𝕜 E := of_fintype_basis ξ
  ξ.equiv_fun.to_linear_map.continuous_of_finite_dimensional
#align continuous_equiv_fun_basis continuous_equiv_fun_basis

namespace LinearMap

variable [T2Space E] [FiniteDimensional 𝕜 E]

/-- The continuous linear map induced by a linear map on a finite dimensional space -/
def toContinuousLinearMap : (E →ₗ[𝕜] F') ≃ₗ[𝕜] E →L[𝕜] F'
    where
  toFun f := ⟨f, f.continuous_of_finite_dimensional⟩
  invFun := coe
  map_add' f g := rfl
  map_smul' c f := rfl
  left_inv f := rfl
  right_inv f := ContinuousLinearMap.coe_injective rfl
#align linear_map.to_continuous_linear_map LinearMap.toContinuousLinearMap

@[simp]
theorem coe_to_continuous_linear_map' (f : E →ₗ[𝕜] F') : ⇑f.toContinuousLinearMap = f :=
  rfl
#align linear_map.coe_to_continuous_linear_map' LinearMap.coe_to_continuous_linear_map'

@[simp]
theorem coe_to_continuous_linear_map (f : E →ₗ[𝕜] F') :
    (f.toContinuousLinearMap : E →ₗ[𝕜] F') = f :=
  rfl
#align linear_map.coe_to_continuous_linear_map LinearMap.coe_to_continuous_linear_map

@[simp]
theorem coe_to_continuous_linear_map_symm :
    ⇑(toContinuousLinearMap : (E →ₗ[𝕜] F') ≃ₗ[𝕜] E →L[𝕜] F').symm = coe :=
  rfl
#align linear_map.coe_to_continuous_linear_map_symm LinearMap.coe_to_continuous_linear_map_symm

@[simp]
theorem det_to_continuous_linear_map (f : E →ₗ[𝕜] E) : f.toContinuousLinearMap.det = f.det :=
  rfl
#align linear_map.det_to_continuous_linear_map LinearMap.det_to_continuous_linear_map

@[simp]
theorem ker_to_continuous_linear_map (f : E →ₗ[𝕜] F') : ker f.toContinuousLinearMap = ker f :=
  rfl
#align linear_map.ker_to_continuous_linear_map LinearMap.ker_to_continuous_linear_map

@[simp]
theorem range_to_continuous_linear_map (f : E →ₗ[𝕜] F') : range f.toContinuousLinearMap = range f :=
  rfl
#align linear_map.range_to_continuous_linear_map LinearMap.range_to_continuous_linear_map

/-- A surjective linear map `f` with finite dimensional codomain is an open map. -/
theorem is_open_map_of_finite_dimensional (f : F →ₗ[𝕜] E) (hf : Function.Surjective f) :
    IsOpenMap f :=
  by
  rcases f.exists_right_inverse_of_surjective (LinearMap.range_eq_top.2 hf) with ⟨g, hg⟩
  refine' IsOpenMap.of_sections fun x => ⟨fun y => g (y - f x) + x, _, _, fun y => _⟩
  ·
    exact
      ((g.continuous_of_finite_dimensional.comp <| continuous_id.sub continuous_const).add
          continuous_const).ContinuousAt
  · rw [sub_self, map_zero, zero_add]
  · simp only [map_sub, map_add, ← comp_apply f g, hg, id_apply, sub_add_cancel]
#align linear_map.is_open_map_of_finite_dimensional LinearMap.is_open_map_of_finite_dimensional

instance canLiftContinuousLinearMap : CanLift (E →ₗ[𝕜] F) (E →L[𝕜] F) coe fun _ => True :=
  ⟨fun f _ => ⟨f.toContinuousLinearMap, rfl⟩⟩
#align linear_map.can_lift_continuous_linear_map LinearMap.canLiftContinuousLinearMap

end LinearMap

namespace LinearEquiv

variable [T2Space E] [T2Space F] [FiniteDimensional 𝕜 E]

/-- The continuous linear equivalence induced by a linear equivalence on a finite dimensional
space. -/
def toContinuousLinearEquiv (e : E ≃ₗ[𝕜] F) : E ≃L[𝕜] F :=
  { e with
    continuous_to_fun := e.toLinearMap.continuous_of_finite_dimensional
    continuous_inv_fun :=
      haveI : FiniteDimensional 𝕜 F := e.finite_dimensional
      e.symm.to_linear_map.continuous_of_finite_dimensional }
#align linear_equiv.to_continuous_linear_equiv LinearEquiv.toContinuousLinearEquiv

@[simp]
theorem coe_to_continuous_linear_equiv (e : E ≃ₗ[𝕜] F) :
    (e.toContinuousLinearEquiv : E →ₗ[𝕜] F) = e :=
  rfl
#align linear_equiv.coe_to_continuous_linear_equiv LinearEquiv.coe_to_continuous_linear_equiv

@[simp]
theorem coe_to_continuous_linear_equiv' (e : E ≃ₗ[𝕜] F) : (e.toContinuousLinearEquiv : E → F) = e :=
  rfl
#align linear_equiv.coe_to_continuous_linear_equiv' LinearEquiv.coe_to_continuous_linear_equiv'

@[simp]
theorem coe_to_continuous_linear_equiv_symm (e : E ≃ₗ[𝕜] F) :
    (e.toContinuousLinearEquiv.symm : F →ₗ[𝕜] E) = e.symm :=
  rfl
#align
  linear_equiv.coe_to_continuous_linear_equiv_symm LinearEquiv.coe_to_continuous_linear_equiv_symm

@[simp]
theorem coe_to_continuous_linear_equiv_symm' (e : E ≃ₗ[𝕜] F) :
    (e.toContinuousLinearEquiv.symm : F → E) = e.symm :=
  rfl
#align
  linear_equiv.coe_to_continuous_linear_equiv_symm' LinearEquiv.coe_to_continuous_linear_equiv_symm'

@[simp]
theorem to_linear_equiv_to_continuous_linear_equiv (e : E ≃ₗ[𝕜] F) :
    e.toContinuousLinearEquiv.toLinearEquiv = e :=
  by
  ext x
  rfl
#align
  linear_equiv.to_linear_equiv_to_continuous_linear_equiv LinearEquiv.to_linear_equiv_to_continuous_linear_equiv

@[simp]
theorem to_linear_equiv_to_continuous_linear_equiv_symm (e : E ≃ₗ[𝕜] F) :
    e.toContinuousLinearEquiv.symm.toLinearEquiv = e.symm :=
  by
  ext x
  rfl
#align
  linear_equiv.to_linear_equiv_to_continuous_linear_equiv_symm LinearEquiv.to_linear_equiv_to_continuous_linear_equiv_symm

instance canLiftContinuousLinearEquiv :
    CanLift (E ≃ₗ[𝕜] F) (E ≃L[𝕜] F) ContinuousLinearEquiv.toLinearEquiv fun _ => True :=
  ⟨fun f _ => ⟨_, f.to_linear_equiv_to_continuous_linear_equiv⟩⟩
#align linear_equiv.can_lift_continuous_linear_equiv LinearEquiv.canLiftContinuousLinearEquiv

end LinearEquiv

namespace ContinuousLinearMap

variable [T2Space E] [FiniteDimensional 𝕜 E]

/-- Builds a continuous linear equivalence from a continuous linear map on a finite-dimensional
vector space whose determinant is nonzero. -/
def toContinuousLinearEquivOfDetNeZero (f : E →L[𝕜] E) (hf : f.det ≠ 0) : E ≃L[𝕜] E :=
  ((f : E →ₗ[𝕜] E).equivOfDetNeZero hf).toContinuousLinearEquiv
#align
  continuous_linear_map.to_continuous_linear_equiv_of_det_ne_zero ContinuousLinearMap.toContinuousLinearEquivOfDetNeZero

@[simp]
theorem coe_to_continuous_linear_equiv_of_det_ne_zero (f : E →L[𝕜] E) (hf : f.det ≠ 0) :
    (f.toContinuousLinearEquivOfDetNeZero hf : E →L[𝕜] E) = f :=
  by
  ext x
  rfl
#align
  continuous_linear_map.coe_to_continuous_linear_equiv_of_det_ne_zero ContinuousLinearMap.coe_to_continuous_linear_equiv_of_det_ne_zero

@[simp]
theorem to_continuous_linear_equiv_of_det_ne_zero_apply (f : E →L[𝕜] E) (hf : f.det ≠ 0) (x : E) :
    f.toContinuousLinearEquivOfDetNeZero hf x = f x :=
  rfl
#align
  continuous_linear_map.to_continuous_linear_equiv_of_det_ne_zero_apply ContinuousLinearMap.to_continuous_linear_equiv_of_det_ne_zero_apply

/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `«expr!![ » -/
/- ./././Mathport/Syntax/Translate/Expr.lean:390:14: unsupported user notation matrix.notation -/
theorem Matrix.to_lin_fin_two_prod_to_continuous_linear_map (a b c d : 𝕜) :
    (Matrix.toLin (Basis.finTwoProd 𝕜) (Basis.finTwoProd 𝕜)
          («expr!![ »
            "./././Mathport/Syntax/Translate/Expr.lean:390:14: unsupported user notation matrix.notation")).toContinuousLinearMap =
      (a • ContinuousLinearMap.fst 𝕜 𝕜 𝕜 + b • ContinuousLinearMap.snd 𝕜 𝕜 𝕜).Prod
        (c • ContinuousLinearMap.fst 𝕜 𝕜 𝕜 + d • ContinuousLinearMap.snd 𝕜 𝕜 𝕜) :=
  ContinuousLinearMap.ext <| Matrix.to_lin_fin_two_prod_apply _ _ _ _
#align
  matrix.to_lin_fin_two_prod_to_continuous_linear_map Matrix.to_lin_fin_two_prod_to_continuous_linear_map

end ContinuousLinearMap

end NormedField

