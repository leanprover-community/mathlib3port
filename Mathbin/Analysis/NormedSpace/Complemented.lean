/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov

! This file was ported from Lean 3 source module analysis.normed_space.complemented
! leanprover-community/mathlib commit 1b0a28e1c93409dbf6d69526863cd9984ef652ce
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Analysis.NormedSpace.Banach
import Mathbin.Analysis.NormedSpace.FiniteDimension

/-!
# Complemented subspaces of normed vector spaces

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

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

/- warning: continuous_linear_map.ker_closed_complemented_of_finite_dimensional_range -> ContinuousLinearMap.ker_closedComplemented_of_finiteDimensional_range is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align continuous_linear_map.ker_closed_complemented_of_finite_dimensional_range ContinuousLinearMap.ker_closedComplemented_of_finiteDimensional_rangeₓ'. -/
theorem ker_closedComplemented_of_finiteDimensional_range (f : E →L[𝕜] F)
    [FiniteDimensional 𝕜 (range f)] : (ker f).ClosedComplemented :=
  by
  set f' : E →L[𝕜] range f := f.cod_restrict _ (f : E →ₗ[𝕜] F).mem_range_self
  rcases f'.exists_right_inverse_of_surjective (f : E →ₗ[𝕜] F).range_rangeRestrict with ⟨g, hg⟩
  simpa only [ker_cod_restrict] using f'.closed_complemented_ker_of_right_inverse g (ext_iff.1 hg)
#align continuous_linear_map.ker_closed_complemented_of_finite_dimensional_range ContinuousLinearMap.ker_closedComplemented_of_finiteDimensional_range

end

variable [CompleteSpace E] [CompleteSpace (F × G)]

/- warning: continuous_linear_map.equiv_prod_of_surjective_of_is_compl -> ContinuousLinearMap.equivProdOfSurjectiveOfIsCompl is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align continuous_linear_map.equiv_prod_of_surjective_of_is_compl ContinuousLinearMap.equivProdOfSurjectiveOfIsComplₓ'. -/
/-- If `f : E →L[R] F` and `g : E →L[R] G` are two surjective linear maps and
their kernels are complement of each other, then `x ↦ (f x, g x)` defines
a linear equivalence `E ≃L[R] F × G`. -/
def equivProdOfSurjectiveOfIsCompl (f : E →L[𝕜] F) (g : E →L[𝕜] G) (hf : range f = ⊤)
    (hg : range g = ⊤) (hfg : IsCompl (ker f) (ker g)) : E ≃L[𝕜] F × G :=
  ((f : E →ₗ[𝕜] F).equivProdOfSurjectiveOfIsCompl (↑g) hf hg
        hfg).toContinuousLinearEquivOfContinuous
    (f.Continuous.prod_mk g.Continuous)
#align continuous_linear_map.equiv_prod_of_surjective_of_is_compl ContinuousLinearMap.equivProdOfSurjectiveOfIsCompl

/- warning: continuous_linear_map.coe_equiv_prod_of_surjective_of_is_compl -> ContinuousLinearMap.coe_equivProdOfSurjectiveOfIsCompl is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align continuous_linear_map.coe_equiv_prod_of_surjective_of_is_compl ContinuousLinearMap.coe_equivProdOfSurjectiveOfIsComplₓ'. -/
@[simp]
theorem coe_equivProdOfSurjectiveOfIsCompl {f : E →L[𝕜] F} {g : E →L[𝕜] G} (hf : range f = ⊤)
    (hg : range g = ⊤) (hfg : IsCompl (ker f) (ker g)) :
    (equivProdOfSurjectiveOfIsCompl f g hf hg hfg : E →ₗ[𝕜] F × G) = f.Prod g :=
  rfl
#align continuous_linear_map.coe_equiv_prod_of_surjective_of_is_compl ContinuousLinearMap.coe_equivProdOfSurjectiveOfIsCompl

/- warning: continuous_linear_map.equiv_prod_of_surjective_of_is_compl_to_linear_equiv -> ContinuousLinearMap.equivProdOfSurjectiveOfIsCompl_toLinearEquiv is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align continuous_linear_map.equiv_prod_of_surjective_of_is_compl_to_linear_equiv ContinuousLinearMap.equivProdOfSurjectiveOfIsCompl_toLinearEquivₓ'. -/
@[simp]
theorem equivProdOfSurjectiveOfIsCompl_toLinearEquiv {f : E →L[𝕜] F} {g : E →L[𝕜] G}
    (hf : range f = ⊤) (hg : range g = ⊤) (hfg : IsCompl (ker f) (ker g)) :
    (equivProdOfSurjectiveOfIsCompl f g hf hg hfg).toLinearEquiv =
      LinearMap.equivProdOfSurjectiveOfIsCompl f g hf hg hfg :=
  rfl
#align continuous_linear_map.equiv_prod_of_surjective_of_is_compl_to_linear_equiv ContinuousLinearMap.equivProdOfSurjectiveOfIsCompl_toLinearEquiv

/- warning: continuous_linear_map.equiv_prod_of_surjective_of_is_compl_apply -> ContinuousLinearMap.equivProdOfSurjectiveOfIsCompl_apply is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align continuous_linear_map.equiv_prod_of_surjective_of_is_compl_apply ContinuousLinearMap.equivProdOfSurjectiveOfIsCompl_applyₓ'. -/
@[simp]
theorem equivProdOfSurjectiveOfIsCompl_apply {f : E →L[𝕜] F} {g : E →L[𝕜] G} (hf : range f = ⊤)
    (hg : range g = ⊤) (hfg : IsCompl (ker f) (ker g)) (x : E) :
    equivProdOfSurjectiveOfIsCompl f g hf hg hfg x = (f x, g x) :=
  rfl
#align continuous_linear_map.equiv_prod_of_surjective_of_is_compl_apply ContinuousLinearMap.equivProdOfSurjectiveOfIsCompl_apply

end ContinuousLinearMap

namespace Subspace

variable [CompleteSpace E] (p q : Subspace 𝕜 E)

/- warning: subspace.prod_equiv_of_closed_compl -> Subspace.prodEquivOfClosedCompl is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align subspace.prod_equiv_of_closed_compl Subspace.prodEquivOfClosedComplₓ'. -/
/-- If `q` is a closed complement of a closed subspace `p`, then `p × q` is continuously
isomorphic to `E`. -/
def prodEquivOfClosedCompl (h : IsCompl p q) (hp : IsClosed (p : Set E))
    (hq : IsClosed (q : Set E)) : (p × q) ≃L[𝕜] E :=
  by
  haveI := hp.complete_space_coe; haveI := hq.complete_space_coe
  refine' (p.prod_equiv_of_is_compl q h).toContinuousLinearEquivOfContinuous _
  exact (p.subtypeL.coprod q.subtypeL).Continuous
#align subspace.prod_equiv_of_closed_compl Subspace.prodEquivOfClosedCompl

/- warning: subspace.linear_proj_of_closed_compl -> Subspace.linearProjOfClosedCompl is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align subspace.linear_proj_of_closed_compl Subspace.linearProjOfClosedComplₓ'. -/
/-- Projection to a closed submodule along a closed complement. -/
def linearProjOfClosedCompl (h : IsCompl p q) (hp : IsClosed (p : Set E))
    (hq : IsClosed (q : Set E)) : E →L[𝕜] p :=
  ContinuousLinearMap.fst 𝕜 p q ∘L ↑(prodEquivOfClosedCompl p q h hp hq).symm
#align subspace.linear_proj_of_closed_compl Subspace.linearProjOfClosedCompl

variable {p q}

/- warning: subspace.coe_prod_equiv_of_closed_compl -> Subspace.coe_prodEquivOfClosedCompl is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align subspace.coe_prod_equiv_of_closed_compl Subspace.coe_prodEquivOfClosedComplₓ'. -/
@[simp]
theorem coe_prodEquivOfClosedCompl (h : IsCompl p q) (hp : IsClosed (p : Set E))
    (hq : IsClosed (q : Set E)) :
    ⇑(p.prodEquivOfClosedCompl q h hp hq) = p.prodEquivOfIsCompl q h :=
  rfl
#align subspace.coe_prod_equiv_of_closed_compl Subspace.coe_prodEquivOfClosedCompl

/- warning: subspace.coe_prod_equiv_of_closed_compl_symm -> Subspace.coe_prodEquivOfClosedCompl_symm is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align subspace.coe_prod_equiv_of_closed_compl_symm Subspace.coe_prodEquivOfClosedCompl_symmₓ'. -/
@[simp]
theorem coe_prodEquivOfClosedCompl_symm (h : IsCompl p q) (hp : IsClosed (p : Set E))
    (hq : IsClosed (q : Set E)) :
    ⇑(p.prodEquivOfClosedCompl q h hp hq).symm = (p.prodEquivOfIsCompl q h).symm :=
  rfl
#align subspace.coe_prod_equiv_of_closed_compl_symm Subspace.coe_prodEquivOfClosedCompl_symm

/- warning: subspace.coe_continuous_linear_proj_of_closed_compl -> Subspace.coe_continuous_linearProjOfClosedCompl is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align subspace.coe_continuous_linear_proj_of_closed_compl Subspace.coe_continuous_linearProjOfClosedComplₓ'. -/
@[simp]
theorem coe_continuous_linearProjOfClosedCompl (h : IsCompl p q) (hp : IsClosed (p : Set E))
    (hq : IsClosed (q : Set E)) :
    (p.linearProjOfClosedCompl q h hp hq : E →ₗ[𝕜] p) = p.linearProjOfIsCompl q h :=
  rfl
#align subspace.coe_continuous_linear_proj_of_closed_compl Subspace.coe_continuous_linearProjOfClosedCompl

/- warning: subspace.coe_continuous_linear_proj_of_closed_compl' -> Subspace.coe_continuous_linearProjOfClosedCompl' is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align subspace.coe_continuous_linear_proj_of_closed_compl' Subspace.coe_continuous_linearProjOfClosedCompl'ₓ'. -/
@[simp]
theorem coe_continuous_linearProjOfClosedCompl' (h : IsCompl p q) (hp : IsClosed (p : Set E))
    (hq : IsClosed (q : Set E)) :
    ⇑(p.linearProjOfClosedCompl q h hp hq) = p.linearProjOfIsCompl q h :=
  rfl
#align subspace.coe_continuous_linear_proj_of_closed_compl' Subspace.coe_continuous_linearProjOfClosedCompl'

/- warning: subspace.closed_complemented_of_closed_compl -> Subspace.closedComplemented_of_closed_compl is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align subspace.closed_complemented_of_closed_compl Subspace.closedComplemented_of_closed_complₓ'. -/
theorem closedComplemented_of_closed_compl (h : IsCompl p q) (hp : IsClosed (p : Set E))
    (hq : IsClosed (q : Set E)) : p.ClosedComplemented :=
  ⟨p.linearProjOfClosedCompl q h hp hq, Submodule.linearProjOfIsCompl_apply_left h⟩
#align subspace.closed_complemented_of_closed_compl Subspace.closedComplemented_of_closed_compl

/- warning: subspace.closed_complemented_iff_has_closed_compl -> Subspace.closedComplemented_iff_has_closed_compl is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align subspace.closed_complemented_iff_has_closed_compl Subspace.closedComplemented_iff_has_closed_complₓ'. -/
theorem closedComplemented_iff_has_closed_compl :
    p.ClosedComplemented ↔
      IsClosed (p : Set E) ∧ ∃ (q : Subspace 𝕜 E)(hq : IsClosed (q : Set E)), IsCompl p q :=
  ⟨fun h => ⟨h.IsClosed, h.has_closed_complement⟩, fun ⟨hp, ⟨q, hq, hpq⟩⟩ =>
    closedComplemented_of_closed_compl hpq hp hq⟩
#align subspace.closed_complemented_iff_has_closed_compl Subspace.closedComplemented_iff_has_closed_compl

/- warning: subspace.closed_complemented_of_quotient_finite_dimensional -> Subspace.closedComplemented_of_quotient_finiteDimensional is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align subspace.closed_complemented_of_quotient_finite_dimensional Subspace.closedComplemented_of_quotient_finiteDimensionalₓ'. -/
theorem closedComplemented_of_quotient_finiteDimensional [CompleteSpace 𝕜]
    [FiniteDimensional 𝕜 (E ⧸ p)] (hp : IsClosed (p : Set E)) : p.ClosedComplemented :=
  by
  obtain ⟨q, hq⟩ : ∃ q, IsCompl p q := p.exists_is_compl
  haveI : FiniteDimensional 𝕜 q := (p.quotient_equiv_of_is_compl q hq).FiniteDimensional
  exact closed_complemented_of_closed_compl hq hp q.closed_of_finite_dimensional
#align subspace.closed_complemented_of_quotient_finite_dimensional Subspace.closedComplemented_of_quotient_finiteDimensional

end Subspace

