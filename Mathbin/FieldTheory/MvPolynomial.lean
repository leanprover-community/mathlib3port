import Mathbin.RingTheory.MvPolynomial.Basic

/-!
# Multivariate polynomials over fields

This file contains basic facts about multivariate polynomials over fields, for example that the
dimension of the space of multivariate polynomials over a field is equal to the cardinality of
finitely supported functions from the indexing set to `ℕ`.
-/


noncomputable theory

open_locale Classical

open Set LinearMap Submodule

open_locale BigOperators

namespace MvPolynomial

universe u v

variable {σ : Type u} {K : Type v}

variable (σ K) [Field K]

-- error in FieldTheory.MvPolynomial: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem quotient_mk_comp_C_injective
(I : ideal (mv_polynomial σ K))
(hI : «expr ≠ »(I, «expr⊤»())) : function.injective ((ideal.quotient.mk I).comp mv_polynomial.C) :=
begin
  refine [expr (ring_hom.injective_iff _).2 (λ x hx, _)],
  rw ["[", expr ring_hom.comp_apply, ",", expr ideal.quotient.eq_zero_iff_mem, "]"] ["at", ident hx],
  refine [expr classical.by_contradiction (λ hx0, absurd (I.eq_top_iff_one.2 _) hI)],
  have [] [] [":=", expr I.mul_mem_left (mv_polynomial.C «expr ⁻¹»(x)) hx],
  rwa ["[", "<-", expr mv_polynomial.C.map_mul, ",", expr inv_mul_cancel hx0, ",", expr mv_polynomial.C_1, "]"] ["at", ident this]
end

end MvPolynomial

namespace MvPolynomial

universe u

variable {σ : Type u} {K : Type u} [Field K]

open_locale Classical

theorem dim_mv_polynomial : Module.rank K (MvPolynomial σ K) = Cardinal.mk (σ →₀ ℕ) :=
  by 
    rw [←Cardinal.lift_inj, ←(basis_monomials σ K).mk_eq_dim]

end MvPolynomial

