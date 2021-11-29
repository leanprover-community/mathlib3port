import Mathbin.Algebra.CharP.Basic 
import Mathbin.LinearAlgebra.FinsuppVectorSpace

/-!
# Multivariate polynomials over commutative rings

This file contains basic facts about multivariate polynomials over commutative rings, for example
that the monomials form a basis.

## Main definitions

* `restrict_total_degree σ R m`: the subspace of multivariate polynomials indexed by `σ` over the
  commutative ring `R` of total degree at most `m`.
* `restrict_degree σ R m`: the subspace of multivariate polynomials indexed by `σ` over the
  commutative ring `R` such that the degree in each individual variable is at most `m`.

## Main statements

* The multivariate polynomial ring over a commutative ring of positive characteristic has positive
  characteristic.
* `basis_monomials`: shows that the monomials form a basis of the vector space of multivariate
  polynomials.

## TODO

Generalise to noncommutative (semi)rings
-/


noncomputable theory

open_locale Classical

open Set LinearMap Submodule

open_locale BigOperators

universe u v

variable(σ : Type u)(R : Type v)[CommRingₓ R](p m : ℕ)

namespace MvPolynomial

section CharP

instance  [CharP R p] : CharP (MvPolynomial σ R) p :=
  { cast_eq_zero_iff :=
      fun n =>
        by 
          rw [←C_eq_coe_nat, ←C_0, C_inj, CharP.cast_eq_zero_iff R p] }

end CharP

section Homomorphism

theorem map_range_eq_map {R S : Type _} [CommRingₓ R] [CommRingₓ S] (p : MvPolynomial σ R) (f : R →+* S) :
  Finsupp.mapRange f f.map_zero p = map f p :=
  by 
    change Finsupp.mapRange (f : R →+ S) (f : R →+ S).map_zero p = map f p 
    rw [p.as_sum, Finsupp.map_range_finset_sum, (map f).map_sum]
    refine' Finset.sum_congr rfl fun n _ => _ 
    rw [map_monomial, ←single_eq_monomial, Finsupp.map_range_single, single_eq_monomial, f.coe_add_monoid_hom]

end Homomorphism

section Degree

/-- The submodule of polynomials of total degree less than or equal to `m`.-/
def restrict_total_degree : Submodule R (MvPolynomial σ R) :=
  Finsupp.supported _ _ { n | (n.sum fun n e => e) ≤ m }

/-- The submodule of polynomials such that the degree with respect to each individual variable is
less than or equal to `m`.-/
def restrict_degree (m : ℕ) : Submodule R (MvPolynomial σ R) :=
  Finsupp.supported _ _ { n | ∀ i, n i ≤ m }

variable{R}

theorem mem_restrict_total_degree (p : MvPolynomial σ R) : p ∈ restrict_total_degree σ R m ↔ p.total_degree ≤ m :=
  by 
    rw [total_degree, Finset.sup_le_iff]
    rfl

theorem mem_restrict_degree (p : MvPolynomial σ R) (n : ℕ) :
  p ∈ restrict_degree σ R n ↔ ∀ s (_ : s ∈ p.support), ∀ i, (s : σ →₀ ℕ) i ≤ n :=
  by 
    rw [restrict_degree, Finsupp.mem_supported]
    rfl

theorem mem_restrict_degree_iff_sup (p : MvPolynomial σ R) (n : ℕ) :
  p ∈ restrict_degree σ R n ↔ ∀ i, p.degrees.count i ≤ n :=
  by 
    simp only [mem_restrict_degree, degrees, Multiset.count_sup, Finsupp.count_to_multiset, Finset.sup_le_iff]
    exact ⟨fun h n s hs => h s hs n, fun h s hs n => h n s hs⟩

variable(σ R)

/-- The monomials form a basis on `mv_polynomial σ R`. -/
def basis_monomials : Basis (σ →₀ ℕ) R (MvPolynomial σ R) :=
  Finsupp.basisSingleOne

@[simp]
theorem coe_basis_monomials : (basis_monomials σ R : (σ →₀ ℕ) → MvPolynomial σ R) = fun s => monomial s 1 :=
  rfl

-- error in RingTheory.MvPolynomial.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
theorem linear_independent_X : linear_independent R (X : σ → mv_polynomial σ R) :=
(basis_monomials σ R).linear_independent.comp (λ s : σ, finsupp.single s 1) (finsupp.single_left_injective one_ne_zero)

end Degree

end MvPolynomial

namespace Polynomial

/-- The monomials form a basis on `polynomial R`. -/
noncomputable def basis_monomials : Basis ℕ R (Polynomial R) :=
  Finsupp.basisSingleOne.map (to_finsupp_iso_alg R).toLinearEquiv.symm

@[simp]
theorem coe_basis_monomials : (basis_monomials R : ℕ → Polynomial R) = fun s => monomial s 1 :=
  _root_.funext$ fun n => to_finsupp_iso_symm_single

end Polynomial

