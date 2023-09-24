/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
import Algebra.CharP.Basic
import Data.Polynomial.AlgebraMap
import Data.MvPolynomial.Variables
import LinearAlgebra.FinsuppVectorSpace

#align_import ring_theory.mv_polynomial.basic from "leanprover-community/mathlib"@"2f5b500a507264de86d666a5f87ddb976e2d8de4"

/-!
# Multivariate polynomials over commutative rings

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

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


noncomputable section

open Set LinearMap Submodule

open scoped BigOperators Polynomial

universe u v

variable (σ : Type u) (R : Type v) [CommRing R] (p m : ℕ)

namespace MvPolynomial

section CharP

instance [CharP R p] : CharP (MvPolynomial σ R) p
    where cast_eq_zero_iff n := by rw [← C_eq_coe_nat, ← C_0, C_inj, CharP.cast_eq_zero_iff R p]

end CharP

section Homomorphism

#print MvPolynomial.mapRange_eq_map /-
theorem mapRange_eq_map {R S : Type _} [CommRing R] [CommRing S] (p : MvPolynomial σ R)
    (f : R →+* S) : Finsupp.mapRange f f.map_zero p = map f p :=
  by
  -- `finsupp.map_range_finset_sum` expects `f : R →+ S`
  change Finsupp.mapRange (f : R →+ S) (f : R →+ S).map_zero p = map f p
  rw [p.as_sum, Finsupp.mapRange_finset_sum, (map f).map_sum]
  refine' Finset.sum_congr rfl fun n _ => _
  rw [map_monomial, ← single_eq_monomial, Finsupp.mapRange_single, single_eq_monomial,
    f.coe_add_monoid_hom]
#align mv_polynomial.map_range_eq_map MvPolynomial.mapRange_eq_map
-/

end Homomorphism

section Degree

#print MvPolynomial.restrictTotalDegree /-
/-- The submodule of polynomials of total degree less than or equal to `m`.-/
def restrictTotalDegree : Submodule R (MvPolynomial σ R) :=
  Finsupp.supported _ _ {n | (n.Sum fun n e => e) ≤ m}
#align mv_polynomial.restrict_total_degree MvPolynomial.restrictTotalDegree
-/

#print MvPolynomial.restrictDegree /-
/-- The submodule of polynomials such that the degree with respect to each individual variable is
less than or equal to `m`.-/
def restrictDegree (m : ℕ) : Submodule R (MvPolynomial σ R) :=
  Finsupp.supported _ _ {n | ∀ i, n i ≤ m}
#align mv_polynomial.restrict_degree MvPolynomial.restrictDegree
-/

variable {R}

#print MvPolynomial.mem_restrictTotalDegree /-
theorem mem_restrictTotalDegree (p : MvPolynomial σ R) :
    p ∈ restrictTotalDegree σ R m ↔ p.totalDegree ≤ m :=
  by
  rw [total_degree, Finset.sup_le_iff]
  rfl
#align mv_polynomial.mem_restrict_total_degree MvPolynomial.mem_restrictTotalDegree
-/

#print MvPolynomial.mem_restrictDegree /-
theorem mem_restrictDegree (p : MvPolynomial σ R) (n : ℕ) :
    p ∈ restrictDegree σ R n ↔ ∀ s ∈ p.support, ∀ i, (s : σ →₀ ℕ) i ≤ n :=
  by
  rw [restrict_degree, Finsupp.mem_supported]
  rfl
#align mv_polynomial.mem_restrict_degree MvPolynomial.mem_restrictDegree
-/

#print MvPolynomial.mem_restrictDegree_iff_sup /-
theorem mem_restrictDegree_iff_sup [DecidableEq σ] (p : MvPolynomial σ R) (n : ℕ) :
    p ∈ restrictDegree σ R n ↔ ∀ i, p.degrees.count i ≤ n :=
  by
  simp only [mem_restrict_degree, degrees_def, Multiset.count_finset_sup, Finsupp.count_toMultiset,
    Finset.sup_le_iff]
  exact ⟨fun h n s hs => h s hs n, fun h s hs n => h n s hs⟩
#align mv_polynomial.mem_restrict_degree_iff_sup MvPolynomial.mem_restrictDegree_iff_sup
-/

variable (σ R)

#print MvPolynomial.basisMonomials /-
/-- The monomials form a basis on `mv_polynomial σ R`. -/
def basisMonomials : Basis (σ →₀ ℕ) R (MvPolynomial σ R) :=
  Finsupp.basisSingleOne
#align mv_polynomial.basis_monomials MvPolynomial.basisMonomials
-/

#print MvPolynomial.coe_basisMonomials /-
@[simp]
theorem coe_basisMonomials :
    (basisMonomials σ R : (σ →₀ ℕ) → MvPolynomial σ R) = fun s => monomial s 1 :=
  rfl
#align mv_polynomial.coe_basis_monomials MvPolynomial.coe_basisMonomials
-/

#print MvPolynomial.linearIndependent_X /-
theorem linearIndependent_X : LinearIndependent R (X : σ → MvPolynomial σ R) :=
  (basisMonomials σ R).LinearIndependent.comp (fun s : σ => Finsupp.single s 1)
    (Finsupp.single_left_injective one_ne_zero)
#align mv_polynomial.linear_independent_X MvPolynomial.linearIndependent_X
-/

end Degree

end MvPolynomial

-- this is here to avoid import cycle issues
namespace Polynomial

#print Polynomial.basisMonomials /-
/-- The monomials form a basis on `R[X]`. -/
noncomputable def basisMonomials : Basis ℕ R R[X] :=
  Basis.ofRepr (toFinsuppIsoAlg R).toLinearEquiv
#align polynomial.basis_monomials Polynomial.basisMonomials
-/

#print Polynomial.coe_basisMonomials /-
@[simp]
theorem coe_basisMonomials : (basisMonomials R : ℕ → R[X]) = fun s => monomial s 1 :=
  funext fun n => ofFinsupp_single _ _
#align polynomial.coe_basis_monomials Polynomial.coe_basisMonomials
-/

end Polynomial

