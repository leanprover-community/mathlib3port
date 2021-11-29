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


variable {𝕜 : Type _} [NondiscreteNormedField 𝕜] {E : Type _} [NormedGroup E] [NormedSpace 𝕜 E] {F : Type _}
  [NormedGroup F] [NormedSpace 𝕜 F] {G : Type _} [NormedGroup G] [NormedSpace 𝕜 G]

noncomputable theory

namespace ContinuousLinearMap

section 

variable [CompleteSpace 𝕜]

theorem ker_closed_complemented_of_finite_dimensional_range (f : E →L[𝕜] F) [FiniteDimensional 𝕜 f.range] :
  f.ker.closed_complemented :=
  by 
    set f' : E →L[𝕜] f.range := f.cod_restrict _ (f : E →ₗ[𝕜] F).mem_range_self 
    rcases f'.exists_right_inverse_of_surjective (f : E →ₗ[𝕜] F).range_range_restrict with ⟨g, hg⟩
    simpa only [ker_cod_restrict] using f'.closed_complemented_ker_of_right_inverse g (ext_iff.1 hg)

end 

variable [CompleteSpace E] [CompleteSpace (F × G)]

/-- If `f : E →L[R] F` and `g : E →L[R] G` are two surjective linear maps and
their kernels are complement of each other, then `x ↦ (f x, g x)` defines
a linear equivalence `E ≃L[R] F × G`. -/
def equiv_prod_of_surjective_of_is_compl (f : E →L[𝕜] F) (g : E →L[𝕜] G) (hf : f.range = ⊤) (hg : g.range = ⊤)
  (hfg : IsCompl f.ker g.ker) : E ≃L[𝕜] F × G :=
  ((f : E →ₗ[𝕜] F).equivProdOfSurjectiveOfIsCompl («expr↑ » g) hf hg hfg).toContinuousLinearEquivOfContinuous
    (f.continuous.prod_mk g.continuous)

@[simp]
theorem coe_equiv_prod_of_surjective_of_is_compl {f : E →L[𝕜] F} {g : E →L[𝕜] G} (hf : f.range = ⊤) (hg : g.range = ⊤)
  (hfg : IsCompl f.ker g.ker) : (equiv_prod_of_surjective_of_is_compl f g hf hg hfg : E →ₗ[𝕜] F × G) = f.prod g :=
  rfl

@[simp]
theorem equiv_prod_of_surjective_of_is_compl_to_linear_equiv {f : E →L[𝕜] F} {g : E →L[𝕜] G} (hf : f.range = ⊤)
  (hg : g.range = ⊤) (hfg : IsCompl f.ker g.ker) :
  (equiv_prod_of_surjective_of_is_compl f g hf hg hfg).toLinearEquiv =
    LinearMap.equivProdOfSurjectiveOfIsCompl f g hf hg hfg :=
  rfl

@[simp]
theorem equiv_prod_of_surjective_of_is_compl_apply {f : E →L[𝕜] F} {g : E →L[𝕜] G} (hf : f.range = ⊤) (hg : g.range = ⊤)
  (hfg : IsCompl f.ker g.ker) (x : E) : equiv_prod_of_surjective_of_is_compl f g hf hg hfg x = (f x, g x) :=
  rfl

end ContinuousLinearMap

namespace Subspace

variable [CompleteSpace E] (p q : Subspace 𝕜 E)

open continuous_linear_map(subtype_val)

-- error in Analysis.NormedSpace.Complemented: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- If `q` is a closed complement of a closed subspace `p`, then `p × q` is continuously
isomorphic to `E`. -/
def prod_equiv_of_closed_compl
(h : is_compl p q)
(hp : is_closed (p : set E))
(hq : is_closed (q : set E)) : «expr ≃L[ ] »(«expr × »(p, q), 𝕜, E) :=
begin
  haveI [] [] [":=", expr hp.complete_space_coe],
  haveI [] [] [":=", expr hq.complete_space_coe],
  refine [expr (p.prod_equiv_of_is_compl q h).to_continuous_linear_equiv_of_continuous _],
  exact [expr ((subtype_val p).coprod (subtype_val q)).continuous]
end

/-- Projection to a closed submodule along a closed complement. -/
def linear_proj_of_closed_compl (h : IsCompl p q) (hp : IsClosed (p : Set E)) (hq : IsClosed (q : Set E)) : E →L[𝕜] p :=
  ContinuousLinearMap.fst 𝕜 p q ∘L «expr↑ » (prod_equiv_of_closed_compl p q h hp hq).symm

variable {p q}

@[simp]
theorem coe_prod_equiv_of_closed_compl (h : IsCompl p q) (hp : IsClosed (p : Set E)) (hq : IsClosed (q : Set E)) :
  «expr⇑ » (p.prod_equiv_of_closed_compl q h hp hq) = p.prod_equiv_of_is_compl q h :=
  rfl

@[simp]
theorem coe_prod_equiv_of_closed_compl_symm (h : IsCompl p q) (hp : IsClosed (p : Set E)) (hq : IsClosed (q : Set E)) :
  «expr⇑ » (p.prod_equiv_of_closed_compl q h hp hq).symm = (p.prod_equiv_of_is_compl q h).symm :=
  rfl

@[simp]
theorem coe_continuous_linear_proj_of_closed_compl (h : IsCompl p q) (hp : IsClosed (p : Set E))
  (hq : IsClosed (q : Set E)) : (p.linear_proj_of_closed_compl q h hp hq : E →ₗ[𝕜] p) = p.linear_proj_of_is_compl q h :=
  rfl

@[simp]
theorem coe_continuous_linear_proj_of_closed_compl' (h : IsCompl p q) (hp : IsClosed (p : Set E))
  (hq : IsClosed (q : Set E)) : «expr⇑ » (p.linear_proj_of_closed_compl q h hp hq) = p.linear_proj_of_is_compl q h :=
  rfl

theorem closed_complemented_of_closed_compl (h : IsCompl p q) (hp : IsClosed (p : Set E)) (hq : IsClosed (q : Set E)) :
  p.closed_complemented :=
  ⟨p.linear_proj_of_closed_compl q h hp hq, Submodule.linear_proj_of_is_compl_apply_left h⟩

theorem closed_complemented_iff_has_closed_compl :
  p.closed_complemented ↔ IsClosed (p : Set E) ∧ ∃ (q : Subspace 𝕜 E)(hq : IsClosed (q : Set E)), IsCompl p q :=
  ⟨fun h => ⟨h.is_closed, h.has_closed_complement⟩,
    fun ⟨hp, ⟨q, hq, hpq⟩⟩ => closed_complemented_of_closed_compl hpq hp hq⟩

-- error in Analysis.NormedSpace.Complemented: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem closed_complemented_of_quotient_finite_dimensional
[complete_space 𝕜]
[finite_dimensional 𝕜 p.quotient]
(hp : is_closed (p : set E)) : p.closed_complemented :=
begin
  obtain ["⟨", ident q, ",", ident hq, "⟩", ":", expr «expr∃ , »((q), is_compl p q), ":=", expr p.exists_is_compl],
  haveI [] [":", expr finite_dimensional 𝕜 q] [":=", expr (p.quotient_equiv_of_is_compl q hq).finite_dimensional],
  exact [expr closed_complemented_of_closed_compl hq hp q.closed_of_finite_dimensional]
end

end Subspace

