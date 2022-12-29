/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov

! This file was ported from Lean 3 source module analysis.normed_space.complemented
! leanprover-community/mathlib commit 422e70f7ce183d2900c586a8cda8381e788a0c62
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Analysis.NormedSpace.Banach
import Mathbin.Analysis.NormedSpace.FiniteDimension

/-!
# Complemented subspaces of normed vector spaces

A submodule `p` of a topological module `E` over `R` is called *complemented* if there exists
a continuous linear projection `f : E →ₗ[R] p`, `∀ x : p, f x = x`. We prove that for
a closed subspace of a normed space this condition is equivalent to existence of a closed
subspace `q` such that `p ⊓ q = ⊥`, `p ⊔ q = ⊤`. We also prove that a subspace of finite codimension
is always a complemented subspace.

## Tags

complemented subspace, normed vector space
-/


variable {𝕜 E F G : Type _} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedAddCommGroup G] [NormedSpace 𝕜 G]

noncomputable section

open LinearMap (ker range)

namespace ContinuousLinearMap

section

variable [CompleteSpace 𝕜]

theorem kerClosedComplementedOfFiniteDimensionalRange (f : E →L[𝕜] F)
    [FiniteDimensional 𝕜 (range f)] : (ker f).ClosedComplemented :=
  by
  set f' : E →L[𝕜] range f := f.cod_restrict _ (f : E →ₗ[𝕜] F).mem_range_self
  rcases f'.exists_right_inverse_of_surjective (f : E →ₗ[𝕜] F).range_range_restrict with ⟨g, hg⟩
  simpa only [ker_cod_restrict] using f'.closed_complemented_ker_of_right_inverse g (ext_iff.1 hg)
#align
  continuous_linear_map.ker_closed_complemented_of_finite_dimensional_range ContinuousLinearMap.kerClosedComplementedOfFiniteDimensionalRange

end

variable [CompleteSpace E] [CompleteSpace (F × G)]

/-- If `f : E →L[R] F` and `g : E →L[R] G` are two surjective linear maps and
their kernels are complement of each other, then `x ↦ (f x, g x)` defines
a linear equivalence `E ≃L[R] F × G`. -/
def equivProdOfSurjectiveOfIsCompl (f : E →L[𝕜] F) (g : E →L[𝕜] G) (hf : range f = ⊤)
    (hg : range g = ⊤) (hfg : IsCompl (ker f) (ker g)) : E ≃L[𝕜] F × G :=
  ((f : E →ₗ[𝕜] F).equivProdOfSurjectiveOfIsCompl (↑g) hf hg
        hfg).toContinuousLinearEquivOfContinuous
    (f.Continuous.prod_mk g.Continuous)
#align
  continuous_linear_map.equiv_prod_of_surjective_of_is_compl ContinuousLinearMap.equivProdOfSurjectiveOfIsCompl

@[simp]
theorem coe_equiv_prod_of_surjective_of_is_compl {f : E →L[𝕜] F} {g : E →L[𝕜] G} (hf : range f = ⊤)
    (hg : range g = ⊤) (hfg : IsCompl (ker f) (ker g)) :
    (equivProdOfSurjectiveOfIsCompl f g hf hg hfg : E →ₗ[𝕜] F × G) = f.Prod g :=
  rfl
#align
  continuous_linear_map.coe_equiv_prod_of_surjective_of_is_compl ContinuousLinearMap.coe_equiv_prod_of_surjective_of_is_compl

@[simp]
theorem equiv_prod_of_surjective_of_is_compl_to_linear_equiv {f : E →L[𝕜] F} {g : E →L[𝕜] G}
    (hf : range f = ⊤) (hg : range g = ⊤) (hfg : IsCompl (ker f) (ker g)) :
    (equivProdOfSurjectiveOfIsCompl f g hf hg hfg).toLinearEquiv =
      LinearMap.equivProdOfSurjectiveOfIsCompl f g hf hg hfg :=
  rfl
#align
  continuous_linear_map.equiv_prod_of_surjective_of_is_compl_to_linear_equiv ContinuousLinearMap.equiv_prod_of_surjective_of_is_compl_to_linear_equiv

@[simp]
theorem equiv_prod_of_surjective_of_is_compl_apply {f : E →L[𝕜] F} {g : E →L[𝕜] G}
    (hf : range f = ⊤) (hg : range g = ⊤) (hfg : IsCompl (ker f) (ker g)) (x : E) :
    equivProdOfSurjectiveOfIsCompl f g hf hg hfg x = (f x, g x) :=
  rfl
#align
  continuous_linear_map.equiv_prod_of_surjective_of_is_compl_apply ContinuousLinearMap.equiv_prod_of_surjective_of_is_compl_apply

end ContinuousLinearMap

namespace Subspace

variable [CompleteSpace E] (p q : Subspace 𝕜 E)

/-- If `q` is a closed complement of a closed subspace `p`, then `p × q` is continuously
isomorphic to `E`. -/
def prodEquivOfClosedCompl (h : IsCompl p q) (hp : IsClosed (p : Set E))
    (hq : IsClosed (q : Set E)) : (p × q) ≃L[𝕜] E :=
  by
  haveI := hp.complete_space_coe; haveI := hq.complete_space_coe
  refine' (p.prod_equiv_of_is_compl q h).toContinuousLinearEquivOfContinuous _
  exact (p.subtypeL.coprod q.subtypeL).Continuous
#align subspace.prod_equiv_of_closed_compl Subspace.prodEquivOfClosedCompl

/-- Projection to a closed submodule along a closed complement. -/
def linearProjOfClosedCompl (h : IsCompl p q) (hp : IsClosed (p : Set E))
    (hq : IsClosed (q : Set E)) : E →L[𝕜] p :=
  ContinuousLinearMap.fst 𝕜 p q ∘L ↑(prodEquivOfClosedCompl p q h hp hq).symm
#align subspace.linear_proj_of_closed_compl Subspace.linearProjOfClosedCompl

variable {p q}

@[simp]
theorem coe_prod_equiv_of_closed_compl (h : IsCompl p q) (hp : IsClosed (p : Set E))
    (hq : IsClosed (q : Set E)) :
    ⇑(p.prodEquivOfClosedCompl q h hp hq) = p.prodEquivOfIsCompl q h :=
  rfl
#align subspace.coe_prod_equiv_of_closed_compl Subspace.coe_prod_equiv_of_closed_compl

@[simp]
theorem coe_prod_equiv_of_closed_compl_symm (h : IsCompl p q) (hp : IsClosed (p : Set E))
    (hq : IsClosed (q : Set E)) :
    ⇑(p.prodEquivOfClosedCompl q h hp hq).symm = (p.prodEquivOfIsCompl q h).symm :=
  rfl
#align subspace.coe_prod_equiv_of_closed_compl_symm Subspace.coe_prod_equiv_of_closed_compl_symm

@[simp]
theorem coe_continuous_linear_proj_of_closed_compl (h : IsCompl p q) (hp : IsClosed (p : Set E))
    (hq : IsClosed (q : Set E)) :
    (p.linearProjOfClosedCompl q h hp hq : E →ₗ[𝕜] p) = p.linearProjOfIsCompl q h :=
  rfl
#align
  subspace.coe_continuous_linear_proj_of_closed_compl Subspace.coe_continuous_linear_proj_of_closed_compl

@[simp]
theorem coe_continuous_linear_proj_of_closed_compl' (h : IsCompl p q) (hp : IsClosed (p : Set E))
    (hq : IsClosed (q : Set E)) :
    ⇑(p.linearProjOfClosedCompl q h hp hq) = p.linearProjOfIsCompl q h :=
  rfl
#align
  subspace.coe_continuous_linear_proj_of_closed_compl' Subspace.coe_continuous_linear_proj_of_closed_compl'

theorem closedComplementedOfClosedCompl (h : IsCompl p q) (hp : IsClosed (p : Set E))
    (hq : IsClosed (q : Set E)) : p.ClosedComplemented :=
  ⟨p.linearProjOfClosedCompl q h hp hq, Submodule.linear_proj_of_is_compl_apply_left h⟩
#align subspace.closed_complemented_of_closed_compl Subspace.closedComplementedOfClosedCompl

theorem closed_complemented_iff_has_closed_compl :
    p.ClosedComplemented ↔
      IsClosed (p : Set E) ∧ ∃ (q : Subspace 𝕜 E)(hq : IsClosed (q : Set E)), IsCompl p q :=
  ⟨fun h => ⟨h.IsClosed, h.has_closed_complement⟩, fun ⟨hp, ⟨q, hq, hpq⟩⟩ =>
    closedComplementedOfClosedCompl hpq hp hq⟩
#align
  subspace.closed_complemented_iff_has_closed_compl Subspace.closed_complemented_iff_has_closed_compl

theorem closedComplementedOfQuotientFiniteDimensional [CompleteSpace 𝕜]
    [FiniteDimensional 𝕜 (E ⧸ p)] (hp : IsClosed (p : Set E)) : p.ClosedComplemented :=
  by
  obtain ⟨q, hq⟩ : ∃ q, IsCompl p q := p.exists_is_compl
  haveI : FiniteDimensional 𝕜 q := (p.quotient_equiv_of_is_compl q hq).FiniteDimensional
  exact closed_complemented_of_closed_compl hq hp q.closed_of_finite_dimensional
#align
  subspace.closed_complemented_of_quotient_finite_dimensional Subspace.closedComplementedOfQuotientFiniteDimensional

end Subspace

