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

variable {R : Type _} [Semiringₓ R]

variable {F E₁ : Type _} [SemiNormedGroup F] [NormedGroup E₁] [Module R E₁]

variable {R₁ : Type _} [Field R₁] [Module R₁ E₁] [Module R₁ F] [FiniteDimensional R₁ E₁] [FiniteDimensional R₁ F]

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

variable {𝕜 : Type _} {V₁ V₂ : Type _} {P₁ P₂ : Type _} [NormedField 𝕜] [NormedGroup V₁] [SemiNormedGroup V₂]
  [NormedSpace 𝕜 V₁] [SemiNormedSpace 𝕜 V₂] [MetricSpace P₁] [PseudoMetricSpace P₂] [NormedAddTorsor V₁ P₁]
  [SemiNormedAddTorsor V₂ P₂]

variable [FiniteDimensional 𝕜 V₁] [FiniteDimensional 𝕜 V₂]

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

-- error in Analysis.NormedSpace.FiniteDimension: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- A linear map on `ι → 𝕜` (where `ι` is a fintype) is continuous -/
theorem linear_map.continuous_on_pi
{ι : Type w}
[fintype ι]
{𝕜 : Type u}
[normed_field 𝕜]
{E : Type v}
[add_comm_group E]
[module 𝕜 E]
[topological_space E]
[topological_add_group E]
[has_continuous_smul 𝕜 E]
(f : «expr →ₗ[ ] »(ι → 𝕜, 𝕜, E)) : continuous f :=
begin
  have [] [":", expr «expr = »((f : (ι → 𝕜) → E), λ
    x, «expr∑ , »((i : ι), «expr • »(x i, f (λ j, if «expr = »(i, j) then 1 else 0))))] [],
  by { ext [] [ident x] [],
    exact [expr f.pi_apply_eq_sum_univ x] },
  rw [expr this] [],
  refine [expr continuous_finset_sum _ (λ i hi, _)],
  exact [expr (continuous_apply i).smul continuous_const]
end

-- error in Analysis.NormedSpace.FiniteDimension: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- The space of continuous linear maps between finite-dimensional spaces is finite-dimensional. -/
instance
{𝕜 E F : Type*}
[field 𝕜]
[topological_space 𝕜]
[topological_space E]
[add_comm_group E]
[module 𝕜 E]
[finite_dimensional 𝕜 E]
[topological_space F]
[add_comm_group F]
[module 𝕜 F]
[topological_add_group F]
[has_continuous_smul 𝕜 F]
[finite_dimensional 𝕜 F] : finite_dimensional 𝕜 «expr →L[ ] »(E, 𝕜, F) :=
begin
  haveI [] [":", expr is_noetherian 𝕜 «expr →ₗ[ ] »(E, 𝕜, F)] [":=", expr is_noetherian.iff_fg.mpr (by apply_instance)],
  let [ident I] [":", expr «expr →ₗ[ ] »(«expr →L[ ] »(E, 𝕜, F), 𝕜, «expr →ₗ[ ] »(E, 𝕜, F))] [":=", expr continuous_linear_map.coe_lm 𝕜],
  exact [expr module.finite.of_injective I continuous_linear_map.coe_injective]
end

section CompleteField

variable {𝕜 : Type u} [NondiscreteNormedField 𝕜] {E : Type v} [NormedGroup E] [NormedSpace 𝕜 E] {F : Type w}
  [NormedGroup F] [NormedSpace 𝕜 F] {F' : Type x} [AddCommGroupₓ F'] [Module 𝕜 F'] [TopologicalSpace F']
  [TopologicalAddGroup F'] [HasContinuousSmul 𝕜 F'] [CompleteSpace 𝕜]

-- error in Analysis.NormedSpace.FiniteDimension: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- In finite dimension over a complete field, the canonical identification (in terms of a basis)
with `𝕜^n` together with its sup norm is continuous. This is the nontrivial part in the fact that
all norms are equivalent in finite dimension.

This statement is superceded by the fact that every linear map on a finite-dimensional space is
continuous, in `linear_map.continuous_of_finite_dimensional`. -/
theorem continuous_equiv_fun_basis {ι : Type v} [fintype ι] (ξ : basis ι 𝕜 E) : continuous ξ.equiv_fun :=
begin
  unfreezingI { induction [expr hn, ":", expr fintype.card ι] [] ["with", ident n, ident IH] ["generalizing", ident ι, ident E] },
  { apply [expr linear_map.continuous_of_bound _ 0 (λ x, _)],
    have [] [":", expr «expr = »(ξ.equiv_fun x, 0)] [],
    by { ext [] [ident i] [],
      exact [expr (fintype.card_eq_zero_iff.1 hn).elim i] },
    change [expr «expr ≤ »(«expr∥ ∥»(ξ.equiv_fun x), «expr * »(0, «expr∥ ∥»(x)))] [] [],
    rw [expr this] [],
    simp [] [] [] ["[", expr norm_nonneg, "]"] [] [] },
  { haveI [] [":", expr finite_dimensional 𝕜 E] [":=", expr of_fintype_basis ξ],
    have [ident H₁] [":", expr ∀ s : submodule 𝕜 E, «expr = »(finrank 𝕜 s, n) → is_closed (s : set E)] [],
    { assume [binders (s s_dim)],
      let [ident b] [] [":=", expr basis.of_vector_space 𝕜 s],
      have [ident U] [":", expr uniform_embedding b.equiv_fun.symm.to_equiv] [],
      { have [] [":", expr «expr = »(fintype.card (basis.of_vector_space_index 𝕜 s), n)] [],
        by { rw ["<-", expr s_dim] [],
          exact [expr (finrank_eq_card_basis b).symm] },
        have [] [":", expr continuous b.equiv_fun] [":=", expr IH b this],
        exact [expr b.equiv_fun.symm.uniform_embedding (linear_map.continuous_on_pi _) this] },
      have [] [":", expr is_complete (s : set E)] [],
      from [expr complete_space_coe_iff_is_complete.1 ((complete_space_congr U).1 (by apply_instance))],
      exact [expr this.is_closed] },
    have [ident H₂] [":", expr ∀ f : «expr →ₗ[ ] »(E, 𝕜, 𝕜), continuous f] [],
    { assume [binders (f)],
      have [] [":", expr «expr ∨ »(«expr = »(finrank 𝕜 f.ker, n), «expr = »(finrank 𝕜 f.ker, n.succ))] [],
      { have [ident Z] [] [":=", expr f.finrank_range_add_finrank_ker],
        rw ["[", expr finrank_eq_card_basis ξ, ",", expr hn, "]"] ["at", ident Z],
        by_cases [expr H, ":", expr «expr = »(finrank 𝕜 f.range, 0)],
        { right,
          rw [expr H] ["at", ident Z],
          simpa [] [] [] [] [] ["using", expr Z] },
        { left,
          have [] [":", expr «expr = »(finrank 𝕜 f.range, 1)] [],
          { refine [expr le_antisymm _ (zero_lt_iff.mpr H)],
            simpa [] [] [] ["[", expr finrank_self, "]"] [] ["using", expr f.range.finrank_le] },
          rw ["[", expr this, ",", expr add_comm, ",", expr nat.add_one, "]"] ["at", ident Z],
          exact [expr nat.succ.inj Z] } },
      have [] [":", expr is_closed (f.ker : set E)] [],
      { cases [expr this] [],
        { exact [expr H₁ _ this] },
        { have [] [":", expr «expr = »(f.ker, «expr⊤»())] [],
          by { apply [expr eq_top_of_finrank_eq],
            rw ["[", expr finrank_eq_card_basis ξ, ",", expr hn, ",", expr this, "]"] [] },
          simp [] [] [] ["[", expr this, "]"] [] [] } },
      exact [expr linear_map.continuous_iff_is_closed_ker.2 this] },
    have [] [":", expr ∀
     i : ι, «expr∃ , »((C), «expr ∧ »(«expr ≤ »(0, C), ∀
       x : E, «expr ≤ »(«expr∥ ∥»(ξ.equiv_fun x i), «expr * »(C, «expr∥ ∥»(x)))))] [],
    { assume [binders (i)],
      let [ident f] [":", expr «expr →ₗ[ ] »(E, 𝕜, 𝕜)] [":=", expr «expr ∘ₗ »(linear_map.proj i, «expr↑ »(ξ.equiv_fun))],
      let [ident f'] [":", expr «expr →L[ ] »(E, 𝕜, 𝕜)] [":=", expr { cont := H₂ f, ..f }],
      exact [expr ⟨«expr∥ ∥»(f'), norm_nonneg _, λ x, continuous_linear_map.le_op_norm f' x⟩] },
    choose [] [ident C0] [ident hC0] ["using", expr this],
    let [ident C] [] [":=", expr «expr∑ , »((i), C0 i)],
    have [ident C_nonneg] [":", expr «expr ≤ »(0, C)] [":=", expr finset.sum_nonneg (λ i hi, (hC0 i).1)],
    have [ident C0_le] [":", expr ∀
     i, «expr ≤ »(C0 i, C)] [":=", expr λ i, finset.single_le_sum (λ j hj, (hC0 j).1) (finset.mem_univ _)],
    apply [expr linear_map.continuous_of_bound _ C (λ x, _)],
    rw [expr pi_semi_norm_le_iff] [],
    { exact [expr λ i, le_trans ((hC0 i).2 x) (mul_le_mul_of_nonneg_right (C0_le i) (norm_nonneg _))] },
    { exact [expr mul_nonneg C_nonneg (norm_nonneg _)] } }
end

-- error in Analysis.NormedSpace.FiniteDimension: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Any linear map on a finite dimensional space over a complete field is continuous. -/
theorem linear_map.continuous_of_finite_dimensional
[finite_dimensional 𝕜 E]
(f : «expr →ₗ[ ] »(E, 𝕜, F')) : continuous f :=
begin
  let [ident b] [] [":=", expr basis.of_vector_space 𝕜 E],
  have [ident A] [":", expr continuous b.equiv_fun] [":=", expr continuous_equiv_fun_basis b],
  have [ident B] [":", expr continuous (f.comp (b.equiv_fun.symm : «expr →ₗ[ ] »(basis.of_vector_space_index 𝕜 E → 𝕜, 𝕜, E)))] [":=", expr linear_map.continuous_on_pi _],
  have [] [":", expr continuous «expr ∘ »(f.comp (b.equiv_fun.symm : «expr →ₗ[ ] »(basis.of_vector_space_index 𝕜 E → 𝕜, 𝕜, E)), b.equiv_fun)] [":=", expr B.comp A],
  convert [] [expr this] [],
  ext [] [ident x] [],
  dsimp [] [] [] [],
  rw ["[", expr basis.equiv_fun_symm_apply, ",", expr basis.sum_repr, "]"] []
end

theorem AffineMap.continuous_of_finite_dimensional {PE PF : Type _} [MetricSpace PE] [NormedAddTorsor E PE]
  [MetricSpace PF] [NormedAddTorsor F PF] [FiniteDimensional 𝕜 E] (f : PE →ᵃ[𝕜] PF) : Continuous f :=
  AffineMap.continuous_linear_iff.1 f.linear.continuous_of_finite_dimensional

namespace LinearMap

variable [FiniteDimensional 𝕜 E]

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

-- error in Analysis.NormedSpace.FiniteDimension: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- The continuous linear equivalence induced by a linear equivalence on a finite dimensional
space. -/
def linear_equiv.to_continuous_linear_equiv
[finite_dimensional 𝕜 E]
(e : «expr ≃ₗ[ ] »(E, 𝕜, F)) : «expr ≃L[ ] »(E, 𝕜, F) :=
{ continuous_to_fun := e.to_linear_map.continuous_of_finite_dimensional,
  continuous_inv_fun := begin
    haveI [] [":", expr finite_dimensional 𝕜 F] [":=", expr e.finite_dimensional],
    exact [expr e.symm.to_linear_map.continuous_of_finite_dimensional]
  end,
  ..e }

theorem LinearMap.exists_antilipschitz_with [FiniteDimensional 𝕜 E] (f : E →ₗ[𝕜] F) (hf : f.ker = ⊥) :
  ∃ (K : _)(_ : K > 0), AntilipschitzWith K f :=
  by 
    cases subsingleton_or_nontrivial E <;> skip
    ·
      exact ⟨1, zero_lt_one, AntilipschitzWith.of_subsingleton⟩
    ·
      rw [LinearMap.ker_eq_bot] at hf 
      let e : E ≃L[𝕜] f.range := (LinearEquiv.ofInjective f hf).toContinuousLinearEquiv 
      exact ⟨_, e.nnnorm_symm_pos, e.antilipschitz⟩

-- error in Analysis.NormedSpace.FiniteDimension: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
protected
theorem linear_independent.eventually
{ι}
[fintype ι]
{f : ι → E}
(hf : linear_independent 𝕜 f) : «expr∀ᶠ in , »((g), expr𝓝() f, linear_independent 𝕜 g) :=
begin
  simp [] [] ["only"] ["[", expr fintype.linear_independent_iff', "]"] [] ["at", ident hf, "⊢"],
  rcases [expr linear_map.exists_antilipschitz_with _ hf, "with", "⟨", ident K, ",", ident K0, ",", ident hK, "⟩"],
  have [] [":", expr tendsto (λ
    g : ι → E, «expr∑ , »((i), «expr∥ ∥»(«expr - »(g i, f i)))) (expr𝓝() f) «expr $ »(expr𝓝(), «expr∑ , »((i), «expr∥ ∥»(«expr - »(f i, f i))))] [],
  from [expr tendsto_finset_sum _ (λ
    i hi, «expr $ »(tendsto.norm, ((continuous_apply i).tendsto _).sub tendsto_const_nhds))],
  simp [] [] ["only"] ["[", expr sub_self, ",", expr norm_zero, ",", expr finset.sum_const_zero, "]"] [] ["at", ident this],
  refine [expr (this.eventually «expr $ »(gt_mem_nhds, inv_pos.2 K0)).mono (λ g hg, _)],
  replace [ident hg] [":", expr «expr < »(«expr∑ , »((i), nnnorm «expr - »(g i, f i)), «expr ⁻¹»(K))] [],
  by { rw ["<-", expr nnreal.coe_lt_coe] [],
    push_cast [] [],
    exact [expr hg] },
  rw [expr linear_map.ker_eq_bot] [],
  refine [expr (hK.add_sub_lipschitz_with «expr $ »(lipschitz_with.of_dist_le_mul, λ v u, _) hg).injective],
  simp [] [] ["only"] ["[", expr dist_eq_norm, ",", expr linear_map.lsum_apply, ",", expr pi.sub_apply, ",", expr linear_map.sum_apply, ",", expr linear_map.comp_apply, ",", expr linear_map.proj_apply, ",", expr linear_map.smul_right_apply, ",", expr linear_map.id_apply, ",", "<-", expr finset.sum_sub_distrib, ",", "<-", expr smul_sub, ",", "<-", expr sub_smul, ",", expr nnreal.coe_sum, ",", expr coe_nnnorm, ",", expr finset.sum_mul, "]"] [] [],
  refine [expr norm_sum_le_of_le _ (λ i _, _)],
  rw ["[", expr norm_smul, ",", expr mul_comm, "]"] [],
  exact [expr mul_le_mul_of_nonneg_left (norm_le_pi_norm «expr - »(v, u) i) (norm_nonneg _)]
end

theorem is_open_set_of_linear_independent {ι : Type _} [Fintype ι] : IsOpen { f:ι → E | LinearIndependent 𝕜 f } :=
  is_open_iff_mem_nhds.2$ fun f => LinearIndependent.eventually

-- error in Analysis.NormedSpace.FiniteDimension: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem is_open_set_of_nat_le_rank
(n : exprℕ()) : is_open {f : «expr →L[ ] »(E, 𝕜, F) | «expr ≤ »(«expr↑ »(n), rank (f : «expr →ₗ[ ] »(E, 𝕜, F)))} :=
begin
  simp [] [] ["only"] ["[", expr le_rank_iff_exists_linear_independent_finset, ",", expr set_of_exists, ",", "<-", expr exists_prop, "]"] [] [],
  refine [expr is_open_bUnion (λ t ht, _)],
  have [] [":", expr continuous (λ f : «expr →L[ ] »(E, 𝕜, F), λ x : (t : set E), f x)] [],
  from [expr continuous_pi (λ x, (continuous_linear_map.apply 𝕜 F (x : E)).continuous)],
  exact [expr is_open_set_of_linear_independent.preimage this]
end

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

variable {ι : Type _} [Fintype ι]

-- error in Analysis.NormedSpace.FiniteDimension: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Construct a continuous linear map given the value at a finite basis. -/
def basis.constrL (v : basis ι 𝕜 E) (f : ι → F) : «expr →L[ ] »(E, 𝕜, F) :=
by haveI [] [":", expr finite_dimensional 𝕜 E] [":=", expr finite_dimensional.of_fintype_basis v]; exact [expr (v.constr 𝕜 f).to_continuous_linear_map]

@[simp, normCast]
theorem Basis.coe_constrL (v : Basis ι 𝕜 E) (f : ι → F) : (v.constrL f : E →ₗ[𝕜] F) = v.constr 𝕜 f :=
  rfl

-- error in Analysis.NormedSpace.FiniteDimension: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- The continuous linear equivalence between a vector space over `𝕜` with a finite basis and
functions from its basis indexing type to `𝕜`. -/ def basis.equiv_funL (v : basis ι 𝕜 E) : «expr ≃L[ ] »(E, 𝕜, ι → 𝕜) :=
{ continuous_to_fun := begin
    haveI [] [":", expr finite_dimensional 𝕜 E] [":=", expr finite_dimensional.of_fintype_basis v],
    apply [expr linear_map.continuous_of_finite_dimensional]
  end,
  continuous_inv_fun := begin
    change [expr continuous v.equiv_fun.symm.to_fun] [] [],
    apply [expr linear_map.continuous_of_finite_dimensional]
  end,
  ..v.equiv_fun }

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

-- error in Analysis.NormedSpace.FiniteDimension: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
instance [finite_dimensional 𝕜 E] [second_countable_topology F] : second_countable_topology «expr →L[ ] »(E, 𝕜, F) :=
begin
  set [] [ident d] [] [":="] [expr finite_dimensional.finrank 𝕜 E] [],
  suffices [] [":", expr ∀
   ε «expr > » (0 : exprℝ()), «expr∃ , »((n : «expr →L[ ] »(E, 𝕜, F) → fin d → exprℕ()), ∀
    f g : «expr →L[ ] »(E, 𝕜, F), «expr = »(n f, n g) → «expr ≤ »(dist f g, ε))],
  from [expr metric.second_countable_of_countable_discretization (λ
    ε ε_pos, ⟨fin d → exprℕ(), by apply_instance, this ε ε_pos⟩)],
  intros [ident ε, ident ε_pos],
  obtain ["⟨", ident u, ":", expr exprℕ() → F, ",", ident hu, ":", expr dense_range u, "⟩", ":=", expr exists_dense_seq F],
  let [ident v] [] [":=", expr finite_dimensional.fin_basis 𝕜 E],
  obtain ["⟨", ident C, ":", expr exprℝ(), ",", ident C_pos, ":", expr «expr < »(0, C), ",", ident hC, ":", expr ∀
   {φ : «expr →L[ ] »(E, 𝕜, F)}
   {M : exprℝ()}, «expr ≤ »(0, M) → ∀
   i, «expr ≤ »(«expr∥ ∥»(φ (v i)), M) → «expr ≤ »(«expr∥ ∥»(φ), «expr * »(C, M)), "⟩", ":=", expr v.op_norm_le],
  have [ident h_2C] [":", expr «expr < »(0, «expr * »(2, C))] [":=", expr mul_pos zero_lt_two C_pos],
  have [ident hε2C] [":", expr «expr < »(0, «expr / »(ε, «expr * »(2, C)))] [":=", expr div_pos ε_pos h_2C],
  have [] [":", expr ∀
   φ : «expr →L[ ] »(E, 𝕜, F), «expr∃ , »((n : fin d → exprℕ()), «expr ≤ »(«expr∥ ∥»(«expr - »(φ, «expr $ »(v.constrL, «expr ∘ »(u, n)))), «expr / »(ε, 2)))] [],
  { intros [ident φ],
    have [] [":", expr ∀
     i, «expr∃ , »((n), «expr ≤ »(«expr∥ ∥»(«expr - »(φ (v i), u n)), «expr / »(ε, «expr * »(2, C))))] [],
    { simp [] [] ["only"] ["[", expr norm_sub_rev, "]"] [] [],
      intro [ident i],
      have [] [":", expr «expr ∈ »(φ (v i), closure (range u))] [":=", expr hu _],
      obtain ["⟨", ident n, ",", ident hn, "⟩", ":", expr «expr∃ , »((n), «expr < »(«expr∥ ∥»(«expr - »(u n, φ (v i))), «expr / »(ε, «expr * »(2, C))))],
      { rw [expr mem_closure_iff_nhds_basis metric.nhds_basis_ball] ["at", ident this],
        specialize [expr this «expr / »(ε, «expr * »(2, C)) hε2C],
        simpa [] [] [] ["[", expr dist_eq_norm, "]"] [] [] },
      exact [expr ⟨n, le_of_lt hn⟩] },
    choose [] [ident n] [ident hn] ["using", expr this],
    use [expr n],
    replace [ident hn] [":", expr ∀
     i : fin d, «expr ≤ »(«expr∥ ∥»(«expr - »(φ, «expr $ »(v.constrL, «expr ∘ »(u, n))) (v i)), «expr / »(ε, «expr * »(2, C)))] [],
    by simp [] [] [] ["[", expr hn, "]"] [] [],
    have [] [":", expr «expr = »(«expr * »(C, «expr / »(ε, «expr * »(2, C))), «expr / »(ε, 2))] [],
    { rw ["[", expr eq_div_iff (two_ne_zero : «expr ≠ »((2 : exprℝ()), 0)), ",", expr mul_comm, ",", "<-", expr mul_assoc, ",", expr mul_div_cancel' _ (ne_of_gt h_2C), "]"] [] },
    specialize [expr hC (le_of_lt hε2C) hn],
    rwa [expr this] ["at", ident hC] },
  choose [] [ident n] [ident hn] ["using", expr this],
  set [] [ident Φ] [] [":="] [expr λ φ : «expr →L[ ] »(E, 𝕜, F), «expr $ »(v.constrL, «expr ∘ »(u, n φ))] [],
  change [expr ∀ z, «expr ≤ »(dist z (Φ z), «expr / »(ε, 2))] [] ["at", ident hn],
  use [expr n],
  intros [ident x, ident y, ident hxy],
  calc
    «expr ≤ »(dist x y, «expr + »(dist x (Φ x), dist (Φ x) y)) : dist_triangle _ _ _
    «expr = »(..., «expr + »(dist x (Φ x), dist y (Φ y))) : by simp [] [] [] ["[", expr Φ, ",", expr hxy, ",", expr dist_comm, "]"] [] []
    «expr ≤ »(..., ε) : by linarith [] [] ["[", expr hn x, ",", expr hn y, "]"]
end

variable (𝕜 E)

-- error in Analysis.NormedSpace.FiniteDimension: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem finite_dimensional.complete [finite_dimensional 𝕜 E] : complete_space E :=
begin
  set [] [ident e] [] [":="] [expr continuous_linear_equiv.of_finrank_eq (@finrank_fin_fun 𝕜 _ (finrank 𝕜 E)).symm] [],
  have [] [":", expr uniform_embedding e.to_linear_equiv.to_equiv.symm] [":=", expr e.symm.uniform_embedding],
  exact [expr (complete_space_congr this).1 (by apply_instance)]
end

variable {𝕜 E}

/-- A finite-dimensional subspace is complete. -/
theorem Submodule.complete_of_finite_dimensional (s : Submodule 𝕜 E) [FiniteDimensional 𝕜 s] : IsComplete (s : Set E) :=
  complete_space_coe_iff_is_complete.1 (FiniteDimensional.complete 𝕜 s)

/-- A finite-dimensional subspace is closed. -/
theorem Submodule.closed_of_finite_dimensional (s : Submodule 𝕜 E) [FiniteDimensional 𝕜 s] : IsClosed (s : Set E) :=
  s.complete_of_finite_dimensional.is_closed

section Riesz

-- error in Analysis.NormedSpace.FiniteDimension: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- In an infinite dimensional space, given a finite number of points, one may find a point
with norm at most `R` which is at distance at least `1` of all these points. -/
theorem exists_norm_le_le_norm_sub_of_finset
{c : 𝕜}
(hc : «expr < »(1, «expr∥ ∥»(c)))
{R : exprℝ()}
(hR : «expr < »(«expr∥ ∥»(c), R))
(h : «expr¬ »(finite_dimensional 𝕜 E))
(s : finset E) : «expr∃ , »((x : E), «expr ∧ »(«expr ≤ »(«expr∥ ∥»(x), R), ∀
  y «expr ∈ » s, «expr ≤ »(1, «expr∥ ∥»(«expr - »(y, x))))) :=
begin
  let [ident F] [] [":=", expr submodule.span 𝕜 (s : set E)],
  haveI [] [":", expr finite_dimensional 𝕜 F] [":=", expr module.finite_def.2 ((submodule.fg_top _).2 (submodule.fg_def.2 ⟨s, finset.finite_to_set _, rfl⟩))],
  have [ident Fclosed] [":", expr is_closed (F : set E)] [":=", expr submodule.closed_of_finite_dimensional _],
  have [] [":", expr «expr∃ , »((x), «expr ∉ »(x, F))] [],
  { contrapose ["!"] [ident h],
    have [] [":", expr «expr = »((«expr⊤»() : submodule 𝕜 E), F)] [],
    by { ext [] [ident x] [],
      simp [] [] [] ["[", expr h, "]"] [] [] },
    have [] [":", expr finite_dimensional 𝕜 («expr⊤»() : submodule 𝕜 E)] [],
    by rwa [expr this] [],
    refine [expr module.finite_def.2 ((submodule.fg_top _).1 (module.finite_def.1 this))] },
  obtain ["⟨", ident x, ",", ident xR, ",", ident hx, "⟩", ":", expr «expr∃ , »((x : E), «expr ∧ »(«expr ≤ »(«expr∥ ∥»(x), R), ∀
     y : E, «expr ∈ »(y, F) → «expr ≤ »(1, «expr∥ ∥»(«expr - »(x, y))))), ":=", expr riesz_lemma_of_norm_lt hc hR Fclosed this],
  have [ident hx'] [":", expr ∀ y : E, «expr ∈ »(y, F) → «expr ≤ »(1, «expr∥ ∥»(«expr - »(y, x)))] [],
  { assume [binders (y hy)],
    rw ["<-", expr norm_neg] [],
    simpa [] [] [] [] [] ["using", expr hx y hy] },
  exact [expr ⟨x, xR, λ y hy, hx' _ (submodule.subset_span hy)⟩]
end

-- error in Analysis.NormedSpace.FiniteDimension: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- In an infinite-dimensional normed space, there exists a sequence of points which are all
bounded by `R` and at distance at least `1`. For a version not assuming `c` and `R`, see
`exists_seq_norm_le_one_le_norm_sub`. -/
theorem exists_seq_norm_le_one_le_norm_sub'
{c : 𝕜}
(hc : «expr < »(1, «expr∥ ∥»(c)))
{R : exprℝ()}
(hR : «expr < »(«expr∥ ∥»(c), R))
(h : «expr¬ »(finite_dimensional 𝕜 E)) : «expr∃ , »((f : exprℕ() → E), «expr ∧ »(∀
  n, «expr ≤ »(«expr∥ ∥»(f n), R), ∀ m n, «expr ≠ »(m, n) → «expr ≤ »(1, «expr∥ ∥»(«expr - »(f m, f n))))) :=
begin
  haveI [] [":", expr is_symm E (λ x y : E, «expr ≤ »(1, «expr∥ ∥»(«expr - »(x, y))))] [],
  { constructor,
    assume [binders (x y hxy)],
    rw ["<-", expr norm_neg] [],
    simpa [] [] [] [] [] [] },
  apply [expr exists_seq_of_forall_finset_exists' (λ
    x : E, «expr ≤ »(«expr∥ ∥»(x), R)) (λ (x : E) (y : E), «expr ≤ »(1, «expr∥ ∥»(«expr - »(x, y))))],
  assume [binders (s hs)],
  exact [expr exists_norm_le_le_norm_sub_of_finset hc hR h s]
end

-- error in Analysis.NormedSpace.FiniteDimension: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem exists_seq_norm_le_one_le_norm_sub
(h : «expr¬ »(finite_dimensional 𝕜 E)) : «expr∃ , »((R : exprℝ())
 (f : exprℕ() → E), «expr ∧ »(«expr < »(1, R), «expr ∧ »(∀
   n, «expr ≤ »(«expr∥ ∥»(f n), R), ∀ m n, «expr ≠ »(m, n) → «expr ≤ »(1, «expr∥ ∥»(«expr - »(f m, f n)))))) :=
begin
  obtain ["⟨", ident c, ",", ident hc, "⟩", ":", expr «expr∃ , »((c : 𝕜), «expr < »(1, «expr∥ ∥»(c))), ":=", expr normed_field.exists_one_lt_norm 𝕜],
  have [ident A] [":", expr «expr < »(«expr∥ ∥»(c), «expr + »(«expr∥ ∥»(c), 1))] [],
  by linarith [] [] [],
  rcases [expr exists_seq_norm_le_one_le_norm_sub' hc A h, "with", "⟨", ident f, ",", ident hf, "⟩"],
  exact [expr ⟨«expr + »(«expr∥ ∥»(c), 1), f, hc.trans A, hf.1, hf.2⟩]
end

variable (𝕜)

-- error in Analysis.NormedSpace.FiniteDimension: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
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

-- error in Analysis.NormedSpace.FiniteDimension: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- An injective linear map with finite-dimensional domain is a closed embedding. -/
theorem linear_equiv.closed_embedding_of_injective
{f : «expr →ₗ[ ] »(E, 𝕜, F)}
(hf : «expr = »(f.ker, «expr⊥»()))
[finite_dimensional 𝕜 E] : closed_embedding «expr⇑ »(f) :=
let g := linear_equiv.of_injective f (linear_map.ker_eq_bot.mp hf) in
{ closed_range := begin
    haveI [] [] [":=", expr f.finite_dimensional_range],
    simpa [] [] [] ["[", expr f.range_coe, "]"] [] ["using", expr f.range.closed_of_finite_dimensional]
  end,
  ..embedding_subtype_coe.comp g.to_continuous_linear_equiv.to_homeomorph.embedding }

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

variable (𝕜 : Type u) [NondiscreteNormedField 𝕜] (E : Type v) [NormedGroup E] [NormedSpace 𝕜 E] [ProperSpace 𝕜]

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

-- error in Analysis.NormedSpace.FiniteDimension: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- In a finite dimensional vector space over `ℝ`, the series `∑ x, ∥f x∥` is unconditionally
summable if and only if the series `∑ x, f x` is unconditionally summable. One implication holds in
any complete normed space, while the other holds only in finite dimensional spaces. -/
theorem summable_norm_iff
{α E : Type*}
[normed_group E]
[normed_space exprℝ() E]
[finite_dimensional exprℝ() E]
{f : α → E} : «expr ↔ »(summable (λ x, «expr∥ ∥»(f x)), summable f) :=
begin
  refine [expr ⟨summable_of_summable_norm, λ hf, _⟩],
  suffices [] [":", expr ∀ {N : exprℕ()} {g : α → fin N → exprℝ()}, summable g → summable (λ x, «expr∥ ∥»(g x))],
  { obtain [ident v, ":=", expr fin_basis exprℝ() E],
    set [] [ident e] [] [":="] [expr v.equiv_funL] [],
    have [] [":", expr summable (λ x, «expr∥ ∥»(e (f x)))] [":=", expr this (e.summable.2 hf)],
    refine [expr summable_of_norm_bounded _ (this.mul_left «expr↑ »(nnnorm (e.symm : «expr →L[ ] »(fin (finrank exprℝ() E) → exprℝ(), exprℝ(), E)))) (λ
      i, _)],
    simpa [] [] [] [] [] ["using", expr (e.symm : «expr →L[ ] »(fin (finrank exprℝ() E) → exprℝ(), exprℝ(), E)).le_op_norm «expr $ »(e, f i)] },
  unfreezingI { clear_dependent [ident E] },
  intros [ident N, ident g, ident hg],
  have [] [":", expr ∀ i, summable (λ x, «expr∥ ∥»(g x i))] [":=", expr λ i, (pi.summable.1 hg i).abs],
  refine [expr summable_of_norm_bounded _ (summable_sum (λ (i) (hi : «expr ∈ »(i, finset.univ)), this i)) (λ x, _)],
  rw ["[", expr norm_norm, ",", expr pi_norm_le_iff, "]"] [],
  { refine [expr λ i, finset.single_le_sum (λ i hi, _) (finset.mem_univ i)],
    exact [expr norm_nonneg (g x i)] },
  { exact [expr finset.sum_nonneg (λ _ _, norm_nonneg _)] }
end

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

