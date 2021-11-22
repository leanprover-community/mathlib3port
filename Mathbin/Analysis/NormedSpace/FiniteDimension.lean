import Mathbin.Analysis.NormedSpace.AffineIsometry 
import Mathbin.Analysis.NormedSpace.OperatorNorm 
import Mathbin.Analysis.Asymptotics.AsymptoticEquivalent 
import Mathbin.LinearAlgebra.Matrix.ToLin

/-!
# Finite dimensional normed spaces over complete fields

Over a complete nondiscrete field, in finite dimension, all norms are equivalent and all linear maps
are continuous. Moreover, a finite-dimensional subspace is always complete and closed.

## Main results:

* `linear_map.continuous_of_finite_dimensional` : a linear map on a finite-dimensional space over a
  complete field is continuous.
* `finite_dimensional.complete` : a finite-dimensional space over a complete field is complete. This
  is not registered as an instance, as the field would be an unknown metavariable in typeclass
  resolution.
* `submodule.closed_of_finite_dimensional` : a finite-dimensional subspace over a complete field is
  closed
* `finite_dimensional.proper` : a finite-dimensional space over a proper field is proper. This
  is not registered as an instance, as the field would be an unknown metavariable in typeclass
  resolution. It is however registered as an instance for `𝕜 = ℝ` and `𝕜 = ℂ`. As properness
  implies completeness, there is no need to also register `finite_dimensional.complete` on `ℝ` or
  `ℂ`.
* `finite_dimensional_of_is_compact_closed_ball`: Riesz' theorem: if the closed unit ball is
  compact, then the space is finite-dimensional.

## Implementation notes

The fact that all norms are equivalent is not written explicitly, as it would mean having two norms
on a single space, which is not the way type classes work. However, if one has a
finite-dimensional vector space `E` with a norm, and a copy `E'` of this type with another norm,
then the identities from `E` to `E'` and from `E'`to `E` are continuous thanks to
`linear_map.continuous_of_finite_dimensional`. This gives the desired norm equivalence.
-/


universe u v w x

noncomputable theory

open Set FiniteDimensional TopologicalSpace Filter Asymptotics

open_locale Classical BigOperators Filter TopologicalSpace Asymptotics

namespace LinearIsometry

open LinearMap

variable{R : Type _}[Semiringₓ R]

variable{F E₁ : Type _}[SemiNormedGroup F][NormedGroup E₁][Module R E₁]

variable{R₁ : Type _}[Field R₁][Module R₁ E₁][Module R₁ F][FiniteDimensional R₁ E₁][FiniteDimensional R₁ F]

/-- A linear isometry between finite dimensional spaces of equal dimension can be upgraded
    to a linear isometry equivalence. -/
def to_linear_isometry_equiv (li : E₁ →ₗᵢ[R₁] F) (h : finrank R₁ E₁ = finrank R₁ F) : E₁ ≃ₗᵢ[R₁] F :=
  { toLinearEquiv := li.to_linear_map.linear_equiv_of_injective li.injective h, norm_map' := li.norm_map' }

@[simp]
theorem coe_to_linear_isometry_equiv (li : E₁ →ₗᵢ[R₁] F) (h : finrank R₁ E₁ = finrank R₁ F) :
  (li.to_linear_isometry_equiv h : E₁ → F) = li :=
  rfl

@[simp]
theorem to_linear_isometry_equiv_apply (li : E₁ →ₗᵢ[R₁] F) (h : finrank R₁ E₁ = finrank R₁ F) (x : E₁) :
  (li.to_linear_isometry_equiv h) x = li x :=
  rfl

end LinearIsometry

namespace AffineIsometry

open AffineMap

variable{𝕜 :
    Type
      _}{V₁ V₂ :
    Type
      _}{P₁ P₂ :
    Type
      _}[NormedField
      𝕜][NormedGroup
      V₁][SemiNormedGroup
      V₂][NormedSpace 𝕜
      V₁][SemiNormedSpace 𝕜 V₂][MetricSpace P₁][PseudoMetricSpace P₂][NormedAddTorsor V₁ P₁][SemiNormedAddTorsor V₂ P₂]

variable[FiniteDimensional 𝕜 V₁][FiniteDimensional 𝕜 V₂]

/-- An affine isometry between finite dimensional spaces of equal dimension can be upgraded
    to an affine isometry equivalence. -/
def to_affine_isometry_equiv [Inhabited P₁] (li : P₁ →ᵃⁱ[𝕜] P₂) (h : finrank 𝕜 V₁ = finrank 𝕜 V₂) : P₁ ≃ᵃⁱ[𝕜] P₂ :=
  AffineIsometryEquiv.mk' li (li.linear_isometry.to_linear_isometry_equiv h) (arbitraryₓ P₁)
    fun p =>
      by 
        simp 

@[simp]
theorem coe_to_affine_isometry_equiv [Inhabited P₁] (li : P₁ →ᵃⁱ[𝕜] P₂) (h : finrank 𝕜 V₁ = finrank 𝕜 V₂) :
  (li.to_affine_isometry_equiv h : P₁ → P₂) = li :=
  rfl

@[simp]
theorem to_affine_isometry_equiv_apply [Inhabited P₁] (li : P₁ →ᵃⁱ[𝕜] P₂) (h : finrank 𝕜 V₁ = finrank 𝕜 V₂) (x : P₁) :
  (li.to_affine_isometry_equiv h) x = li x :=
  rfl

end AffineIsometry

/-- A linear map on `ι → 𝕜` (where `ι` is a fintype) is continuous -/
theorem LinearMap.continuous_on_pi {ι : Type w} [Fintype ι] {𝕜 : Type u} [NormedField 𝕜] {E : Type v} [AddCommGroupₓ E]
  [Module 𝕜 E] [TopologicalSpace E] [TopologicalAddGroup E] [HasContinuousSmul 𝕜 E] (f : (ι → 𝕜) →ₗ[𝕜] E) :
  Continuous f :=
  by 
    have  : (f : (ι → 𝕜) → E) = fun x => ∑i : ι, x i • f fun j => if i = j then 1 else 0
    ·
      ·
        ext x 
        exact f.pi_apply_eq_sum_univ x 
    rw [this]
    refine' continuous_finset_sum _ fun i hi => _ 
    exact (continuous_apply i).smul continuous_const

/-- The space of continuous linear maps between finite-dimensional spaces is finite-dimensional. -/
instance  {𝕜 E F : Type _} [Field 𝕜] [TopologicalSpace 𝕜] [TopologicalSpace E] [AddCommGroupₓ E] [Module 𝕜 E]
  [FiniteDimensional 𝕜 E] [TopologicalSpace F] [AddCommGroupₓ F] [Module 𝕜 F] [TopologicalAddGroup F]
  [HasContinuousSmul 𝕜 F] [FiniteDimensional 𝕜 F] : FiniteDimensional 𝕜 (E →L[𝕜] F) :=
  by 
    haveI  : IsNoetherian 𝕜 (E →ₗ[𝕜] F) :=
      is_noetherian.iff_fg.mpr
        (by 
          infer_instance)
    let I : (E →L[𝕜] F) →ₗ[𝕜] E →ₗ[𝕜] F := ContinuousLinearMap.coeLm 𝕜 
    exact Module.Finite.of_injective I ContinuousLinearMap.coe_injective

section CompleteField

variable{𝕜 :
    Type
      u}[NondiscreteNormedField
      𝕜]{E :
    Type
      v}[NormedGroup
      E][NormedSpace 𝕜
      E]{F :
    Type
      w}[NormedGroup
      F][NormedSpace 𝕜
      F]{F' :
    Type
      x}[AddCommGroupₓ
      F'][Module 𝕜 F'][TopologicalSpace F'][TopologicalAddGroup F'][HasContinuousSmul 𝕜 F'][CompleteSpace 𝕜]

/-- In finite dimension over a complete field, the canonical identification (in terms of a basis)
with `𝕜^n` together with its sup norm is continuous. This is the nontrivial part in the fact that
all norms are equivalent in finite dimension.

This statement is superceded by the fact that every linear map on a finite-dimensional space is
continuous, in `linear_map.continuous_of_finite_dimensional`. -/
theorem continuous_equiv_fun_basis {ι : Type v} [Fintype ι] (ξ : Basis ι 𝕜 E) : Continuous ξ.equiv_fun :=
  by 
    unfreezingI 
      induction' hn : Fintype.card ι with n IH generalizing ι E
    ·
      apply LinearMap.continuous_of_bound _ 0 fun x => _ 
      have  : ξ.equiv_fun x = 0
      ·
        ·
          ext i 
          exact (Fintype.card_eq_zero_iff.1 hn).elim i 
      change ∥ξ.equiv_fun x∥ ≤ 0*∥x∥
      rw [this]
      simp [norm_nonneg]
    ·
      haveI  : FiniteDimensional 𝕜 E := of_fintype_basis ξ 
      have H₁ : ∀ s : Submodule 𝕜 E, finrank 𝕜 s = n → IsClosed (s : Set E)
      ·
        intro s s_dim 
        let b := Basis.ofVectorSpace 𝕜 s 
        have U : UniformEmbedding b.equiv_fun.symm.to_equiv
        ·
          have  : Fintype.card (Basis.OfVectorSpaceIndex 𝕜 s) = n
          ·
            ·
              rw [←s_dim]
              exact (finrank_eq_card_basis b).symm 
          have  : Continuous b.equiv_fun := IH b this 
          exact b.equiv_fun.symm.uniform_embedding (LinearMap.continuous_on_pi _) this 
        have  : IsComplete (s : Set E)
        exact
          complete_space_coe_iff_is_complete.1
            ((complete_space_congr U).1
              (by 
                infer_instance))
        exact this.is_closed 
      have H₂ : ∀ f : E →ₗ[𝕜] 𝕜, Continuous f
      ·
        intro f 
        have  : finrank 𝕜 f.ker = n ∨ finrank 𝕜 f.ker = n.succ
        ·
          have Z := f.finrank_range_add_finrank_ker 
          rw [finrank_eq_card_basis ξ, hn] at Z 
          byCases' H : finrank 𝕜 f.range = 0
          ·
            right 
            rw [H] at Z 
            simpa using Z
          ·
            left 
            have  : finrank 𝕜 f.range = 1
            ·
              refine' le_antisymmₓ _ (zero_lt_iff.mpr H)
              simpa [finrank_self] using f.range.finrank_le 
            rw [this, add_commₓ, Nat.add_one] at Z 
            exact Nat.succ.injₓ Z 
        have  : IsClosed (f.ker : Set E)
        ·
          cases this
          ·
            exact H₁ _ this
          ·
            have  : f.ker = ⊤
            ·
              ·
                apply eq_top_of_finrank_eq 
                rw [finrank_eq_card_basis ξ, hn, this]
            simp [this]
        exact LinearMap.continuous_iff_is_closed_ker.2 this 
      have  : ∀ i : ι, ∃ C, 0 ≤ C ∧ ∀ x : E, ∥ξ.equiv_fun x i∥ ≤ C*∥x∥
      ·
        intro i 
        let f : E →ₗ[𝕜] 𝕜 := LinearMap.proj i ∘ₗ «expr↑ » ξ.equiv_fun 
        let f' : E →L[𝕜] 𝕜 := { f with cont := H₂ f }
        exact ⟨∥f'∥, norm_nonneg _, fun x => ContinuousLinearMap.le_op_norm f' x⟩
      choose C0 hC0 using this 
      let C := ∑i, C0 i 
      have C_nonneg : 0 ≤ C := Finset.sum_nonneg fun i hi => (hC0 i).1
      have C0_le : ∀ i, C0 i ≤ C := fun i => Finset.single_le_sum (fun j hj => (hC0 j).1) (Finset.mem_univ _)
      apply LinearMap.continuous_of_bound _ C fun x => _ 
      rw [pi_semi_norm_le_iff]
      ·
        exact fun i => le_transₓ ((hC0 i).2 x) (mul_le_mul_of_nonneg_right (C0_le i) (norm_nonneg _))
      ·
        exact mul_nonneg C_nonneg (norm_nonneg _)

/-- Any linear map on a finite dimensional space over a complete field is continuous. -/
theorem LinearMap.continuous_of_finite_dimensional [FiniteDimensional 𝕜 E] (f : E →ₗ[𝕜] F') : Continuous f :=
  by 
    let b := Basis.ofVectorSpace 𝕜 E 
    have A : Continuous b.equiv_fun := continuous_equiv_fun_basis b 
    have B : Continuous (f.comp (b.equiv_fun.symm : (Basis.OfVectorSpaceIndex 𝕜 E → 𝕜) →ₗ[𝕜] E)) :=
      LinearMap.continuous_on_pi _ 
    have  : Continuous (f.comp (b.equiv_fun.symm : (Basis.OfVectorSpaceIndex 𝕜 E → 𝕜) →ₗ[𝕜] E) ∘ b.equiv_fun) :=
      B.comp A 
    convert this 
    ext x 
    dsimp 
    rw [Basis.equiv_fun_symm_apply, Basis.sum_repr]

theorem AffineMap.continuous_of_finite_dimensional {PE PF : Type _} [MetricSpace PE] [NormedAddTorsor E PE]
  [MetricSpace PF] [NormedAddTorsor F PF] [FiniteDimensional 𝕜 E] (f : PE →ᵃ[𝕜] PF) : Continuous f :=
  AffineMap.continuous_linear_iff.1 f.linear.continuous_of_finite_dimensional

namespace LinearMap

variable[FiniteDimensional 𝕜 E]

/-- The continuous linear map induced by a linear map on a finite dimensional space -/
def to_continuous_linear_map : (E →ₗ[𝕜] F') ≃ₗ[𝕜] E →L[𝕜] F' :=
  { toFun := fun f => ⟨f, f.continuous_of_finite_dimensional⟩, invFun := coeₓ, map_add' := fun f g => rfl,
    map_smul' := fun c f => rfl, left_inv := fun f => rfl, right_inv := fun f => ContinuousLinearMap.coe_injective rfl }

@[simp]
theorem coe_to_continuous_linear_map' (f : E →ₗ[𝕜] F') : «expr⇑ » f.to_continuous_linear_map = f :=
  rfl

@[simp]
theorem coe_to_continuous_linear_map (f : E →ₗ[𝕜] F') : (f.to_continuous_linear_map : E →ₗ[𝕜] F') = f :=
  rfl

@[simp]
theorem coe_to_continuous_linear_map_symm :
  «expr⇑ » (to_continuous_linear_map : (E →ₗ[𝕜] F') ≃ₗ[𝕜] E →L[𝕜] F').symm = coeₓ :=
  rfl

end LinearMap

/-- The continuous linear equivalence induced by a linear equivalence on a finite dimensional
space. -/
def LinearEquiv.toContinuousLinearEquiv [FiniteDimensional 𝕜 E] (e : E ≃ₗ[𝕜] F) : E ≃L[𝕜] F :=
  { e with continuous_to_fun := e.to_linear_map.continuous_of_finite_dimensional,
    continuous_inv_fun :=
      by 
        haveI  : FiniteDimensional 𝕜 F := e.finite_dimensional 
        exact e.symm.to_linear_map.continuous_of_finite_dimensional }

theorem LinearMap.exists_antilipschitz_with [FiniteDimensional 𝕜 E] (f : E →ₗ[𝕜] F) (hf : f.ker = ⊥) :
  ∃ (K : _)(_ : K > 0), AntilipschitzWith K f :=
  by 
    cases subsingleton_or_nontrivial E <;> resetI
    ·
      exact ⟨1, zero_lt_one, AntilipschitzWith.of_subsingleton⟩
    ·
      rw [LinearMap.ker_eq_bot] at hf 
      let e : E ≃L[𝕜] f.range := (LinearEquiv.ofInjective f hf).toContinuousLinearEquiv 
      exact ⟨_, e.nnnorm_symm_pos, e.antilipschitz⟩

protected theorem LinearIndependent.eventually {ι} [Fintype ι] {f : ι → E} (hf : LinearIndependent 𝕜 f) :
  ∀ᶠg in 𝓝 f, LinearIndependent 𝕜 g :=
  by 
    simp only [Fintype.linear_independent_iff'] at hf⊢
    rcases LinearMap.exists_antilipschitz_with _ hf with ⟨K, K0, hK⟩
    have  : tendsto (fun g : ι → E => ∑i, ∥g i - f i∥) (𝓝 f) (𝓝$ ∑i, ∥f i - f i∥)
    exact tendsto_finset_sum _ fun i hi => tendsto.norm$ ((continuous_apply i).Tendsto _).sub tendsto_const_nhds 
    simp only [sub_self, norm_zero, Finset.sum_const_zero] at this 
    refine' (this.eventually (gt_mem_nhds$ inv_pos.2 K0)).mono fun g hg => _ 
    replace hg : (∑i, nnnorm (g i - f i)) < K⁻¹
    ·
      ·
        rw [←Nnreal.coe_lt_coe]
        pushCast 
        exact hg 
    rw [LinearMap.ker_eq_bot]
    refine' (hK.add_sub_lipschitz_with (LipschitzWith.of_dist_le_mul$ fun v u => _) hg).Injective 
    simp only [dist_eq_norm, LinearMap.lsum_apply, Pi.sub_apply, LinearMap.sum_apply, LinearMap.comp_apply,
      LinearMap.proj_apply, LinearMap.smul_right_apply, LinearMap.id_apply, ←Finset.sum_sub_distrib, ←smul_sub,
      ←sub_smul, Nnreal.coe_sum, coe_nnnorm, Finset.sum_mul]
    refine' norm_sum_le_of_le _ fun i _ => _ 
    rw [norm_smul, mul_commₓ]
    exact mul_le_mul_of_nonneg_left (norm_le_pi_norm (v - u) i) (norm_nonneg _)

theorem is_open_set_of_linear_independent {ι : Type _} [Fintype ι] : IsOpen { f : ι → E | LinearIndependent 𝕜 f } :=
  is_open_iff_mem_nhds.2$ fun f => LinearIndependent.eventually

theorem is_open_set_of_nat_le_rank (n : ℕ) : IsOpen { f : E →L[𝕜] F | «expr↑ » n ≤ rank (f : E →ₗ[𝕜] F) } :=
  by 
    simp only [le_rank_iff_exists_linear_independent_finset, set_of_exists, ←exists_prop]
    refine' is_open_bUnion fun t ht => _ 
    have  : Continuous fun f : E →L[𝕜] F => fun x : (t : Set E) => f x 
    exact continuous_pi fun x => (ContinuousLinearMap.apply 𝕜 F (x : E)).Continuous 
    exact is_open_set_of_linear_independent.preimage this

/-- Two finite-dimensional normed spaces are continuously linearly equivalent if they have the same
(finite) dimension. -/
theorem FiniteDimensional.nonempty_continuous_linear_equiv_of_finrank_eq [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F]
  (cond : finrank 𝕜 E = finrank 𝕜 F) : Nonempty (E ≃L[𝕜] F) :=
  (nonempty_linear_equiv_of_finrank_eq cond).map LinearEquiv.toContinuousLinearEquiv

/-- Two finite-dimensional normed spaces are continuously linearly equivalent if and only if they
have the same (finite) dimension. -/
theorem FiniteDimensional.nonempty_continuous_linear_equiv_iff_finrank_eq [FiniteDimensional 𝕜 E]
  [FiniteDimensional 𝕜 F] : Nonempty (E ≃L[𝕜] F) ↔ finrank 𝕜 E = finrank 𝕜 F :=
  ⟨fun ⟨h⟩ => h.to_linear_equiv.finrank_eq, fun h => FiniteDimensional.nonempty_continuous_linear_equiv_of_finrank_eq h⟩

/-- A continuous linear equivalence between two finite-dimensional normed spaces of the same
(finite) dimension. -/
def ContinuousLinearEquiv.ofFinrankEq [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F]
  (cond : finrank 𝕜 E = finrank 𝕜 F) : E ≃L[𝕜] F :=
  (linear_equiv.of_finrank_eq E F cond).toContinuousLinearEquiv

variable{ι : Type _}[Fintype ι]

/-- Construct a continuous linear map given the value at a finite basis. -/
def Basis.constrL (v : Basis ι 𝕜 E) (f : ι → F) : E →L[𝕜] F :=
  by 
    haveI  : FiniteDimensional 𝕜 E := FiniteDimensional.of_fintype_basis v <;>
      exact (v.constr 𝕜 f).toContinuousLinearMap

@[simp, normCast]
theorem Basis.coe_constrL (v : Basis ι 𝕜 E) (f : ι → F) : (v.constrL f : E →ₗ[𝕜] F) = v.constr 𝕜 f :=
  rfl

/-- The continuous linear equivalence between a vector space over `𝕜` with a finite basis and
functions from its basis indexing type to `𝕜`. -/
def Basis.equivFunL (v : Basis ι 𝕜 E) : E ≃L[𝕜] ι → 𝕜 :=
  { v.equiv_fun with
    continuous_to_fun :=
      by 
        haveI  : FiniteDimensional 𝕜 E := FiniteDimensional.of_fintype_basis v 
        apply LinearMap.continuous_of_finite_dimensional,
    continuous_inv_fun :=
      by 
        change Continuous v.equiv_fun.symm.to_fun 
        apply LinearMap.continuous_of_finite_dimensional }

@[simp]
theorem Basis.constrL_apply (v : Basis ι 𝕜 E) (f : ι → F) (e : E) : (v.constrL f) e = ∑i, v.equiv_fun e i • f i :=
  v.constr_apply_fintype 𝕜 _ _

@[simp]
theorem Basis.constrL_basis (v : Basis ι 𝕜 E) (f : ι → F) (i : ι) : (v.constrL f) (v i) = f i :=
  v.constr_basis 𝕜 _ _

theorem Basis.sup_norm_le_norm (v : Basis ι 𝕜 E) :
  ∃ (C : _)(_ : C > (0 : ℝ)), ∀ e : E, (∑i, ∥v.equiv_fun e i∥) ≤ C*∥e∥ :=
  by 
    set φ := v.equiv_funL.to_continuous_linear_map 
    set C := ∥φ∥*Fintype.card ι 
    use max C 1, lt_of_lt_of_leₓ zero_lt_one (le_max_rightₓ C 1)
    intro e 
    calc (∑i, ∥φ e i∥) ≤ ∑i : ι, ∥φ e∥ :=
      by 
        apply Finset.sum_le_sum 
        exact fun i hi => norm_le_pi_norm (φ e) i _ = ∥φ e∥*Fintype.card ι :=
      by 
        simpa only [mul_commₓ, Finset.sum_const, nsmul_eq_mul]_ ≤ (∥φ∥*∥e∥)*Fintype.card ι :=
      mul_le_mul_of_nonneg_right (φ.le_op_norm e) (Fintype.card ι).cast_nonneg _ = (∥φ∥*Fintype.card ι)*∥e∥ :=
      by 
        ring _ ≤ max C 1*∥e∥ :=
      mul_le_mul_of_nonneg_right (le_max_leftₓ _ _) (norm_nonneg _)

theorem Basis.op_norm_le {ι : Type _} [Fintype ι] (v : Basis ι 𝕜 E) :
  ∃ (C : _)(_ : C > (0 : ℝ)), ∀ {u : E →L[𝕜] F} {M : ℝ}, 0 ≤ M → (∀ i, ∥u (v i)∥ ≤ M) → ∥u∥ ≤ C*M :=
  by 
    obtain ⟨C, C_pos, hC⟩ : ∃ (C : _)(_ : C > (0 : ℝ)), ∀ e : E, (∑i, ∥v.equiv_fun e i∥) ≤ C*∥e∥
    exact v.sup_norm_le_norm 
    use C, C_pos 
    intro u M hM hu 
    apply u.op_norm_le_bound (mul_nonneg (le_of_ltₓ C_pos) hM)
    intro e 
    calc ∥u e∥ = ∥u (∑i, v.equiv_fun e i • v i)∥ :=
      by 
        rw [v.sum_equiv_fun]_ = ∥∑i, v.equiv_fun e i • (u$ v i)∥ :=
      by 
        simp [u.map_sum, LinearMap.map_smul]_ ≤ ∑i, ∥v.equiv_fun e i • (u$ v i)∥ :=
      norm_sum_le _ _ _ = ∑i, ∥v.equiv_fun e i∥*∥u (v i)∥ :=
      by 
        simp only [norm_smul]_ ≤ ∑i, ∥v.equiv_fun e i∥*M :=
      Finset.sum_le_sum fun i hi => mul_le_mul_of_nonneg_left (hu i) (norm_nonneg _)_ = (∑i, ∥v.equiv_fun e i∥)*M :=
      finset.sum_mul.symm _ ≤ (C*∥e∥)*M := mul_le_mul_of_nonneg_right (hC e) hM _ = (C*M)*∥e∥ :=
      by 
        ring

instance  [FiniteDimensional 𝕜 E] [second_countable_topology F] : second_countable_topology (E →L[𝕜] F) :=
  by 
    set d := FiniteDimensional.finrank 𝕜 E 
    suffices  : ∀ ε _ : ε > (0 : ℝ), ∃ n : (E →L[𝕜] F) → Finₓ d → ℕ, ∀ f g : E →L[𝕜] F, n f = n g → dist f g ≤ ε 
    exact
      Metric.second_countable_of_countable_discretization
        fun ε ε_pos =>
          ⟨Finₓ d → ℕ,
            by 
              infer_instance,
            this ε ε_pos⟩
    intro ε ε_pos 
    obtain ⟨u : ℕ → F, hu : DenseRange u⟩ := exists_dense_seq F 
    let v := FiniteDimensional.finBasis 𝕜 E 
    obtain ⟨C : ℝ, C_pos : 0 < C, hC : ∀ {φ : E →L[𝕜] F} {M : ℝ}, 0 ≤ M → (∀ i, ∥φ (v i)∥ ≤ M) → ∥φ∥ ≤ C*M⟩ :=
      v.op_norm_le 
    have h_2C : 0 < 2*C := mul_pos zero_lt_two C_pos 
    have hε2C : 0 < ε / 2*C := div_pos ε_pos h_2C 
    have  : ∀ φ : E →L[𝕜] F, ∃ n : Finₓ d → ℕ, ∥φ - (v.constrL$ (u ∘ n))∥ ≤ ε / 2
    ·
      intro φ 
      have  : ∀ i, ∃ n, ∥φ (v i) - u n∥ ≤ ε / 2*C
      ·
        simp only [norm_sub_rev]
        intro i 
        have  : φ (v i) ∈ Closure (range u) := hu _ 
        obtain ⟨n, hn⟩ : ∃ n, ∥u n - φ (v i)∥ < ε / 2*C
        ·
          rw [mem_closure_iff_nhds_basis Metric.nhds_basis_ball] at this 
          specialize this (ε / 2*C) hε2C 
          simpa [dist_eq_norm]
        exact ⟨n, le_of_ltₓ hn⟩
      choose n hn using this 
      use n 
      replace hn : ∀ i : Finₓ d, ∥(φ - (v.constrL$ (u ∘ n))) (v i)∥ ≤ ε / 2*C
      ·
        simp [hn]
      have  : (C*ε / 2*C) = ε / 2
      ·
        rw [eq_div_iff (two_ne_zero : (2 : ℝ) ≠ 0), mul_commₓ, ←mul_assocₓ, mul_div_cancel' _ (ne_of_gtₓ h_2C)]
      specialize hC (le_of_ltₓ hε2C) hn 
      rwa [this] at hC 
    choose n hn using this 
    set Φ := fun φ : E →L[𝕜] F => v.constrL$ (u ∘ n φ)
    change ∀ z, dist z (Φ z) ≤ ε / 2 at hn 
    use n 
    intro x y hxy 
    calc dist x y ≤ dist x (Φ x)+dist (Φ x) y := dist_triangle _ _ _ _ = dist x (Φ x)+dist y (Φ y) :=
      by 
        simp [Φ, hxy, dist_comm]_ ≤ ε :=
      by 
        linarith [hn x, hn y]

variable(𝕜 E)

theorem FiniteDimensional.complete [FiniteDimensional 𝕜 E] : CompleteSpace E :=
  by 
    set e := ContinuousLinearEquiv.ofFinrankEq (@finrank_fin_fun 𝕜 _ (finrank 𝕜 E)).symm 
    have  : UniformEmbedding e.to_linear_equiv.to_equiv.symm := e.symm.uniform_embedding 
    exact
      (complete_space_congr this).1
        (by 
          infer_instance)

variable{𝕜 E}

/-- A finite-dimensional subspace is complete. -/
theorem Submodule.complete_of_finite_dimensional (s : Submodule 𝕜 E) [FiniteDimensional 𝕜 s] : IsComplete (s : Set E) :=
  complete_space_coe_iff_is_complete.1 (FiniteDimensional.complete 𝕜 s)

/-- A finite-dimensional subspace is closed. -/
theorem Submodule.closed_of_finite_dimensional (s : Submodule 𝕜 E) [FiniteDimensional 𝕜 s] : IsClosed (s : Set E) :=
  s.complete_of_finite_dimensional.is_closed

section Riesz

/-- In an infinite dimensional space, given a finite number of points, one may find a point
with norm at most `R` which is at distance at least `1` of all these points. -/
theorem exists_norm_le_le_norm_sub_of_finset {c : 𝕜} (hc : 1 < ∥c∥) {R : ℝ} (hR : ∥c∥ < R) (h : ¬FiniteDimensional 𝕜 E)
  (s : Finset E) : ∃ x : E, ∥x∥ ≤ R ∧ ∀ y _ : y ∈ s, 1 ≤ ∥y - x∥ :=
  by 
    let F := Submodule.span 𝕜 (s : Set E)
    haveI  : FiniteDimensional 𝕜 F :=
      Module.finite_def.2 ((Submodule.fg_top _).2 (Submodule.fg_def.2 ⟨s, Finset.finite_to_set _, rfl⟩))
    have Fclosed : IsClosed (F : Set E) := Submodule.closed_of_finite_dimensional _ 
    have  : ∃ x, x ∉ F
    ·
      contrapose! h 
      have  : (⊤ : Submodule 𝕜 E) = F
      ·
        ·
          ext x 
          simp [h]
      have  : FiniteDimensional 𝕜 (⊤ : Submodule 𝕜 E)
      ·
        rwa [this]
      refine' Module.finite_def.2 ((Submodule.fg_top _).1 (Module.finite_def.1 this))
    obtain ⟨x, xR, hx⟩ : ∃ x : E, ∥x∥ ≤ R ∧ ∀ y : E, y ∈ F → 1 ≤ ∥x - y∥ := riesz_lemma_of_norm_lt hc hR Fclosed this 
    have hx' : ∀ y : E, y ∈ F → 1 ≤ ∥y - x∥
    ·
      intro y hy 
      rw [←norm_neg]
      simpa using hx y hy 
    exact ⟨x, xR, fun y hy => hx' _ (Submodule.subset_span hy)⟩

/-- In an infinite-dimensional normed space, there exists a sequence of points which are all
bounded by `R` and at distance at least `1`. For a version not assuming `c` and `R`, see
`exists_seq_norm_le_one_le_norm_sub`. -/
theorem exists_seq_norm_le_one_le_norm_sub' {c : 𝕜} (hc : 1 < ∥c∥) {R : ℝ} (hR : ∥c∥ < R) (h : ¬FiniteDimensional 𝕜 E) :
  ∃ f : ℕ → E, (∀ n, ∥f n∥ ≤ R) ∧ ∀ m n, m ≠ n → 1 ≤ ∥f m - f n∥ :=
  by 
    haveI  : IsSymm E fun x y : E => 1 ≤ ∥x - y∥
    ·
      constructor 
      intro x y hxy 
      rw [←norm_neg]
      simpa 
    apply exists_seq_of_forall_finset_exists' (fun x : E => ∥x∥ ≤ R) fun x : E y : E => 1 ≤ ∥x - y∥
    intro s hs 
    exact exists_norm_le_le_norm_sub_of_finset hc hR h s

theorem exists_seq_norm_le_one_le_norm_sub (h : ¬FiniteDimensional 𝕜 E) :
  ∃ (R : ℝ)(f : ℕ → E), 1 < R ∧ (∀ n, ∥f n∥ ≤ R) ∧ ∀ m n, m ≠ n → 1 ≤ ∥f m - f n∥ :=
  by 
    obtain ⟨c, hc⟩ : ∃ c : 𝕜, 1 < ∥c∥ := NormedField.exists_one_lt_norm 𝕜 
    have A : ∥c∥ < ∥c∥+1
    ·
      linarith 
    rcases exists_seq_norm_le_one_le_norm_sub' hc A h with ⟨f, hf⟩
    exact ⟨∥c∥+1, f, hc.trans A, hf.1, hf.2⟩

variable(𝕜)

-- error in Analysis.NormedSpace.FiniteDimension: ././Mathport/Syntax/Translate/Basic.lean:340:40: in by_contra: ././Mathport/Syntax/Translate/Tactic/Basic.lean:41:45: missing argument
/-- Riesz's theorem: if the unit ball is compact in a vector space, then the space is
finite-dimensional. -/
theorem finite_dimensional_of_is_compact_closed_ball
{r : exprℝ()}
(rpos : «expr < »(0, r))
(h : is_compact (metric.closed_ball (0 : E) r)) : finite_dimensional 𝕜 E :=
begin
  by_contra [ident hfin],
  obtain ["⟨", ident R, ",", ident f, ",", ident Rgt, ",", ident fle, ",", ident lef, "⟩", ":", expr «expr∃ , »((R : exprℝ())
    (f : exprℕ() → E), «expr ∧ »(«expr < »(1, R), «expr ∧ »(∀
      n, «expr ≤ »(«expr∥ ∥»(f n), R), ∀
      m
      n, «expr ≠ »(m, n) → «expr ≤ »(1, «expr∥ ∥»(«expr - »(f m, f n)))))), ":=", expr exists_seq_norm_le_one_le_norm_sub hfin],
  have [ident rRpos] [":", expr «expr < »(0, «expr / »(r, R))] [":=", expr div_pos rpos (zero_lt_one.trans Rgt)],
  obtain ["⟨", ident c, ",", ident hc, "⟩", ":", expr «expr∃ , »((c : 𝕜), «expr ∧ »(«expr < »(0, «expr∥ ∥»(c)), «expr < »(«expr∥ ∥»(c), «expr / »(r, R)))), ":=", expr normed_field.exists_norm_lt _ rRpos],
  let [ident g] [] [":=", expr λ n : exprℕ(), «expr • »(c, f n)],
  have [ident A] [":", expr ∀ n, «expr ∈ »(g n, metric.closed_ball (0 : E) r)] [],
  { assume [binders (n)],
    simp [] [] ["only"] ["[", expr norm_smul, ",", expr dist_zero_right, ",", expr metric.mem_closed_ball, "]"] [] [],
    calc
      «expr ≤ »(«expr * »(«expr∥ ∥»(c), «expr∥ ∥»(f n)), «expr * »(«expr / »(r, R), R)) : mul_le_mul hc.2.le (fle n) (norm_nonneg _) rRpos.le
      «expr = »(..., r) : by field_simp [] ["[", expr (zero_lt_one.trans Rgt).ne', "]"] [] [] },
  obtain ["⟨", ident x, ",", ident hx, ",", ident φ, ",", ident φmono, ",", ident φlim, "⟩", ":", expr «expr∃ , »((x : E)
    (H : «expr ∈ »(x, metric.closed_ball (0 : E) r))
    (φ : exprℕ() → exprℕ()), «expr ∧ »(strict_mono φ, tendsto «expr ∘ »(g, φ) at_top (expr𝓝() x))), ":=", expr h.tendsto_subseq A],
  have [ident B] [":", expr cauchy_seq «expr ∘ »(g, φ)] [":=", expr φlim.cauchy_seq],
  obtain ["⟨", ident N, ",", ident hN, "⟩", ":", expr «expr∃ , »((N : exprℕ()), ∀
    n : exprℕ(), «expr ≤ »(N, n) → «expr < »(dist («expr ∘ »(g, φ) n) («expr ∘ »(g, φ) N), «expr∥ ∥»(c))), ":=", expr metric.cauchy_seq_iff'.1 B «expr∥ ∥»(c) hc.1],
  apply [expr lt_irrefl «expr∥ ∥»(c)],
  calc
    «expr ≤ »(«expr∥ ∥»(c), dist (g (φ «expr + »(N, 1))) (g (φ N))) : begin
      conv_lhs [] [] { rw ["[", "<-", expr mul_one «expr∥ ∥»(c), "]"] },
      simp [] [] ["only"] ["[", expr g, ",", expr dist_eq_norm, ",", "<-", expr smul_sub, ",", expr norm_smul, ",", "-", ident mul_one, "]"] [] [],
      apply [expr mul_le_mul_of_nonneg_left (lef _ _ (ne_of_gt _)) (norm_nonneg _)],
      exact [expr φmono (nat.lt_succ_self N)]
    end
    «expr < »(..., «expr∥ ∥»(c)) : hN «expr + »(N, 1) (nat.le_succ N)
end

end Riesz

/-- An injective linear map with finite-dimensional domain is a closed embedding. -/
theorem LinearEquiv.closed_embedding_of_injective {f : E →ₗ[𝕜] F} (hf : f.ker = ⊥) [FiniteDimensional 𝕜 E] :
  ClosedEmbedding («expr⇑ » f) :=
  let g := LinearEquiv.ofInjective f (LinearMap.ker_eq_bot.mp hf)
  { embedding_subtype_coe.comp g.to_continuous_linear_equiv.to_homeomorph.embedding with
    closed_range :=
      by 
        haveI  := f.finite_dimensional_range 
        simpa [f.range_coe] using f.range.closed_of_finite_dimensional }

theorem ContinuousLinearMap.exists_right_inverse_of_surjective [FiniteDimensional 𝕜 F] (f : E →L[𝕜] F)
  (hf : f.range = ⊤) : ∃ g : F →L[𝕜] E, f.comp g = ContinuousLinearMap.id 𝕜 F :=
  let ⟨g, hg⟩ := (f : E →ₗ[𝕜] F).exists_right_inverse_of_surjective hf
  ⟨g.to_continuous_linear_map, ContinuousLinearMap.ext$ LinearMap.ext_iff.1 hg⟩

theorem closed_embedding_smul_left {c : E} (hc : c ≠ 0) : ClosedEmbedding fun x : 𝕜 => x • c :=
  LinearEquiv.closed_embedding_of_injective (LinearEquiv.ker_to_span_singleton 𝕜 E hc)

theorem is_closed_map_smul_left (c : E) : IsClosedMap fun x : 𝕜 => x • c :=
  by 
    byCases' hc : c = 0
    ·
      simpRw [hc, smul_zero]
      exact is_closed_map_const
    ·
      exact (closed_embedding_smul_left hc).IsClosedMap

end CompleteField

section ProperField

variable(𝕜 : Type u)[NondiscreteNormedField 𝕜](E : Type v)[NormedGroup E][NormedSpace 𝕜 E][ProperSpace 𝕜]

/-- Any finite-dimensional vector space over a proper field is proper.
We do not register this as an instance to avoid an instance loop when trying to prove the
properness of `𝕜`, and the search for `𝕜` as an unknown metavariable. Declare the instance
explicitly when needed. -/
theorem FiniteDimensional.proper [FiniteDimensional 𝕜 E] : ProperSpace E :=
  by 
    set e := ContinuousLinearEquiv.ofFinrankEq (@finrank_fin_fun 𝕜 _ (finrank 𝕜 E)).symm 
    exact e.symm.antilipschitz.proper_space e.symm.continuous e.symm.surjective

end ProperField

instance FiniteDimensional.proper_real (E : Type u) [NormedGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] :
  ProperSpace E :=
  FiniteDimensional.proper ℝ E

attribute [instance] FiniteDimensional.proper_real

/-- In a finite dimensional vector space over `ℝ`, the series `∑ x, ∥f x∥` is unconditionally
summable if and only if the series `∑ x, f x` is unconditionally summable. One implication holds in
any complete normed space, while the other holds only in finite dimensional spaces. -/
theorem summable_norm_iff {α E : Type _} [NormedGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] {f : α → E} :
  (Summable fun x => ∥f x∥) ↔ Summable f :=
  by 
    refine' ⟨summable_of_summable_norm, fun hf => _⟩
    suffices  : ∀ {N : ℕ} {g : α → Finₓ N → ℝ}, Summable g → Summable fun x => ∥g x∥
    ·
      obtain v := fin_basis ℝ E 
      set e := v.equiv_funL 
      have  : Summable fun x => ∥e (f x)∥ := this (e.summable.2 hf)
      refine'
        summable_of_norm_bounded _ (this.mul_left («expr↑ » (nnnorm (e.symm : (Finₓ (finrank ℝ E) → ℝ) →L[ℝ] E))))
          fun i => _ 
      simpa using (e.symm : (Finₓ (finrank ℝ E) → ℝ) →L[ℝ] E).le_op_norm (e$ f i)
    unfreezingI 
      clear! E 
    intro N g hg 
    have  : ∀ i, Summable fun x => ∥g x i∥ := fun i => (Pi.summable.1 hg i).abs 
    refine' summable_of_norm_bounded _ (summable_sum fun i hi : i ∈ Finset.univ => this i) fun x => _ 
    rw [norm_norm, pi_norm_le_iff]
    ·
      refine' fun i => Finset.single_le_sum (fun i hi => _) (Finset.mem_univ i)
      exact norm_nonneg (g x i)
    ·
      exact Finset.sum_nonneg fun _ _ => norm_nonneg _

theorem summable_of_is_O' {ι E F : Type _} [NormedGroup E] [CompleteSpace E] [NormedGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F] {f : ι → E} {g : ι → F} (hg : Summable g) (h : is_O f g cofinite) : Summable f :=
  summable_of_is_O (summable_norm_iff.mpr hg) h.norm_right

theorem summable_of_is_O_nat' {E F : Type _} [NormedGroup E] [CompleteSpace E] [NormedGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F] {f : ℕ → E} {g : ℕ → F} (hg : Summable g) (h : is_O f g at_top) : Summable f :=
  summable_of_is_O_nat (summable_norm_iff.mpr hg) h.norm_right

theorem summable_of_is_equivalent {ι E : Type _} [NormedGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] {f : ι → E}
  {g : ι → E} (hg : Summable g) (h : f ~[cofinite] g) : Summable f :=
  hg.trans_sub (summable_of_is_O' hg h.is_o.is_O)

theorem summable_of_is_equivalent_nat {E : Type _} [NormedGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] {f : ℕ → E}
  {g : ℕ → E} (hg : Summable g) (h : f ~[at_top] g) : Summable f :=
  hg.trans_sub (summable_of_is_O_nat' hg h.is_o.is_O)

theorem IsEquivalent.summable_iff {ι E : Type _} [NormedGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] {f : ι → E}
  {g : ι → E} (h : f ~[cofinite] g) : Summable f ↔ Summable g :=
  ⟨fun hf => summable_of_is_equivalent hf h.symm, fun hg => summable_of_is_equivalent hg h⟩

theorem IsEquivalent.summable_iff_nat {E : Type _} [NormedGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] {f : ℕ → E}
  {g : ℕ → E} (h : f ~[at_top] g) : Summable f ↔ Summable g :=
  ⟨fun hf => summable_of_is_equivalent_nat hf h.symm, fun hg => summable_of_is_equivalent_nat hg h⟩

