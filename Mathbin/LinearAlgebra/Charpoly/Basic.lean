import Mathbin.LinearAlgebra.FreeModule.Finite.Basic 
import Mathbin.LinearAlgebra.Matrix.Charpoly.Coeff

/-!

# Characteristic polynomial

We define the characteristic polynomial of `f : M →ₗ[R] M`, where `M` is a finite and
free `R`-module. The proof that `f.charpoly` is the characteristic polynomial of the matrix of `f`
in any basis is in `linear_algebra/charpoly/to_matrix`.

## Main definition

* `linear_map.charpoly f` : the characteristic polynomial of `f : M →ₗ[R] M`.

-/


universe u v w

variable {R : Type u} {M : Type v} [CommRingₓ R] [Nontrivial R]

variable [AddCommGroupₓ M] [Module R M] [Module.Free R M] [Module.Finite R M] (f : M →ₗ[R] M)

open_locale Classical Matrix

noncomputable theory

open Module.Free Polynomial Matrix

namespace LinearMap

section Basic

/-- The characteristic polynomial of `f : M →ₗ[R] M`. -/
def charpoly : Polynomial R :=
  (to_matrix (choose_basis R M) (choose_basis R M) f).charpoly

theorem charpoly_def : f.charpoly = (to_matrix (choose_basis R M) (choose_basis R M) f).charpoly :=
  rfl

end Basic

section Coeff

theorem charpoly_monic : f.charpoly.monic :=
  charpoly_monic _

end Coeff

section CayleyHamilton

/-- The Cayley-Hamilton Theorem, that the characteristic polynomial of a linear map, applied to
the linear map itself, is zero. -/
theorem aeval_self_charpoly : aeval f f.charpoly = 0 :=
  by 
    apply (LinearEquiv.map_eq_zero_iff (algEquivMatrix _).toLinearEquiv).1
    rw [AlgEquiv.to_linear_equiv_apply, ←AlgEquiv.coe_alg_hom, ←Polynomial.aeval_alg_hom_apply _ _ _, charpoly_def]
    exact aeval_self_charpoly _

theorem IsIntegral : IsIntegral R f :=
  ⟨f.charpoly, ⟨charpoly_monic f, aeval_self_charpoly f⟩⟩

theorem minpoly_dvd_charpoly {K : Type u} {M : Type v} [Field K] [AddCommGroupₓ M] [Module K M] [FiniteDimensional K M]
  (f : M →ₗ[K] M) : minpoly K f ∣ f.charpoly :=
  minpoly.dvd _ _ (aeval_self_charpoly f)

variable {f}

-- error in LinearAlgebra.Charpoly.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem minpoly_coeff_zero_of_injective (hf : function.injective f) : «expr ≠ »((minpoly R f).coeff 0, 0) :=
begin
  intro [ident h],
  obtain ["⟨", ident P, ",", ident hP, "⟩", ":=", expr X_dvd_iff.2 h],
  have [ident hdegP] [":", expr «expr < »(P.degree, (minpoly R f).degree)] [],
  { rw ["[", expr hP, ",", expr mul_comm, "]"] [],
    refine [expr degree_lt_degree_mul_X (λ h, _)],
    rw ["[", expr h, ",", expr mul_zero, "]"] ["at", ident hP],
    exact [expr minpoly.ne_zero (is_integral f) hP] },
  have [ident hPmonic] [":", expr P.monic] [],
  { suffices [] [":", expr (minpoly R f).monic],
    { rwa ["[", expr monic.def, ",", expr hP, ",", expr mul_comm, ",", expr leading_coeff_mul_X, ",", "<-", expr monic.def, "]"] ["at", ident this] },
    exact [expr minpoly.monic (is_integral f)] },
  have [ident hzero] [":", expr «expr = »(aeval f (minpoly R f), 0)] [":=", expr minpoly.aeval _ _],
  simp [] [] ["only"] ["[", expr hP, ",", expr mul_eq_comp, ",", expr ext_iff, ",", expr hf, ",", expr aeval_X, ",", expr map_eq_zero_iff, ",", expr coe_comp, ",", expr alg_hom.map_mul, ",", expr zero_apply, "]"] [] ["at", ident hzero],
  exact [expr not_le.2 hdegP (minpoly.min _ _ hPmonic (ext hzero))]
end

end CayleyHamilton

end LinearMap

