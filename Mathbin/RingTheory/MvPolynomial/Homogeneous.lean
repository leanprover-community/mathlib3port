/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Eric Wieser
-/
import Algebra.DirectSum.Internal
import Algebra.GradedMonoid
import Data.MvPolynomial.Variables

#align_import ring_theory.mv_polynomial.homogeneous from "leanprover-community/mathlib"@"1b0a28e1c93409dbf6d69526863cd9984ef652ce"

/-!
# Homogeneous polynomials

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

A multivariate polynomial `φ` is homogeneous of degree `n`
if all monomials occuring in `φ` have degree `n`.

## Main definitions/lemmas

* `is_homogeneous φ n`: a predicate that asserts that `φ` is homogeneous of degree `n`.
* `homogeneous_submodule σ R n`: the submodule of homogeneous polynomials of degree `n`.
* `homogeneous_component n`: the additive morphism that projects polynomials onto
  their summand that is homogeneous of degree `n`.
* `sum_homogeneous_component`: every polynomial is the sum of its homogeneous components

-/


open scoped BigOperators

namespace MvPolynomial

variable {σ : Type _} {τ : Type _} {R : Type _} {S : Type _}

#print MvPolynomial.IsHomogeneous /-
/-
TODO
* create definition for `∑ i in d.support, d i`
* show that `mv_polynomial σ R ≃ₐ[R] ⨁ i, homogeneous_submodule σ R i`
-/
/-- A multivariate polynomial `φ` is homogeneous of degree `n`
if all monomials occuring in `φ` have degree `n`. -/
def IsHomogeneous [CommSemiring R] (φ : MvPolynomial σ R) (n : ℕ) :=
  ∀ ⦃d⦄, coeff d φ ≠ 0 → ∑ i in d.support, d i = n
#align mv_polynomial.is_homogeneous MvPolynomial.IsHomogeneous
-/

variable (σ R)

#print MvPolynomial.homogeneousSubmodule /-
/-- The submodule of homogeneous `mv_polynomial`s of degree `n`. -/
def homogeneousSubmodule [CommSemiring R] (n : ℕ) : Submodule R (MvPolynomial σ R)
    where
  carrier := {x | x.Homogeneous n}
  smul_mem' r a ha c hc := by
    rw [coeff_smul] at hc 
    apply ha
    intro h
    apply hc
    rw [h]
    exact smul_zero r
  zero_mem' d hd := False.elim (hd <| coeff_zero _)
  add_mem' a b ha hb c hc := by
    rw [coeff_add] at hc 
    obtain h | h : coeff c a ≠ 0 ∨ coeff c b ≠ 0 := by contrapose! hc; simp only [hc, add_zero]
    · exact ha h
    · exact hb h
#align mv_polynomial.homogeneous_submodule MvPolynomial.homogeneousSubmodule
-/

variable {σ R}

#print MvPolynomial.mem_homogeneousSubmodule /-
@[simp]
theorem mem_homogeneousSubmodule [CommSemiring R] (n : ℕ) (p : MvPolynomial σ R) :
    p ∈ homogeneousSubmodule σ R n ↔ p.Homogeneous n :=
  Iff.rfl
#align mv_polynomial.mem_homogeneous_submodule MvPolynomial.mem_homogeneousSubmodule
-/

variable (σ R)

#print MvPolynomial.homogeneousSubmodule_eq_finsupp_supported /-
/-- While equal, the former has a convenient definitional reduction. -/
theorem homogeneousSubmodule_eq_finsupp_supported [CommSemiring R] (n : ℕ) :
    homogeneousSubmodule σ R n = Finsupp.supported _ R {d | ∑ i in d.support, d i = n} :=
  by
  ext
  rw [Finsupp.mem_supported, Set.subset_def]
  simp only [Finsupp.mem_support_iff, Finset.mem_coe]
  rfl
#align mv_polynomial.homogeneous_submodule_eq_finsupp_supported MvPolynomial.homogeneousSubmodule_eq_finsupp_supported
-/

variable {σ R}

#print MvPolynomial.homogeneousSubmodule_mul /-
theorem homogeneousSubmodule_mul [CommSemiring R] (m n : ℕ) :
    homogeneousSubmodule σ R m * homogeneousSubmodule σ R n ≤ homogeneousSubmodule σ R (m + n) :=
  by
  rw [Submodule.mul_le]
  intro φ hφ ψ hψ c hc
  rw [coeff_mul] at hc 
  obtain ⟨⟨d, e⟩, hde, H⟩ := Finset.exists_ne_zero_of_sum_ne_zero hc
  have aux : coeff d φ ≠ 0 ∧ coeff e ψ ≠ 0 :=
    by
    contrapose! H
    by_cases h : coeff d φ = 0 <;>
      simp_all only [Ne.def, not_false_iff, MulZeroClass.zero_mul, MulZeroClass.mul_zero]
  specialize hφ aux.1; specialize hψ aux.2
  rw [Finsupp.mem_antidiagonal] at hde 
  classical
#align mv_polynomial.homogeneous_submodule_mul MvPolynomial.homogeneousSubmodule_mul
-/

section

variable [CommSemiring R]

variable {σ R}

#print MvPolynomial.isHomogeneous_monomial /-
theorem isHomogeneous_monomial (d : σ →₀ ℕ) (r : R) (n : ℕ) (hn : ∑ i in d.support, d i = n) :
    IsHomogeneous (monomial d r) n := by
  intro c hc
  classical
#align mv_polynomial.is_homogeneous_monomial MvPolynomial.isHomogeneous_monomial
-/

variable (σ) {R}

#print MvPolynomial.isHomogeneous_of_totalDegree_zero /-
theorem isHomogeneous_of_totalDegree_zero {p : MvPolynomial σ R} (hp : p.totalDegree = 0) :
    IsHomogeneous p 0 := by
  erw [total_degree, Finset.sup_eq_bot_iff] at hp 
  -- we have to do this in two steps to stop simp changing bot to zero
  simp_rw [mem_support_iff] at hp 
  exact hp
#align mv_polynomial.is_homogeneous_of_total_degree_zero MvPolynomial.isHomogeneous_of_totalDegree_zero
-/

#print MvPolynomial.isHomogeneous_C /-
theorem isHomogeneous_C (r : R) : IsHomogeneous (C r : MvPolynomial σ R) 0 :=
  by
  apply is_homogeneous_monomial
  simp only [Finsupp.zero_apply, Finset.sum_const_zero]
#align mv_polynomial.is_homogeneous_C MvPolynomial.isHomogeneous_C
-/

variable (σ R)

#print MvPolynomial.isHomogeneous_zero /-
theorem isHomogeneous_zero (n : ℕ) : IsHomogeneous (0 : MvPolynomial σ R) n :=
  (homogeneousSubmodule σ R n).zero_mem
#align mv_polynomial.is_homogeneous_zero MvPolynomial.isHomogeneous_zero
-/

#print MvPolynomial.isHomogeneous_one /-
theorem isHomogeneous_one : IsHomogeneous (1 : MvPolynomial σ R) 0 :=
  isHomogeneous_C _ _
#align mv_polynomial.is_homogeneous_one MvPolynomial.isHomogeneous_one
-/

variable {σ} (R)

#print MvPolynomial.isHomogeneous_X /-
theorem isHomogeneous_X (i : σ) : IsHomogeneous (X i : MvPolynomial σ R) 1 :=
  by
  apply is_homogeneous_monomial
  simp only [Finsupp.support_single_ne_zero _ one_ne_zero, Finset.sum_singleton]
  exact Finsupp.single_eq_same
#align mv_polynomial.is_homogeneous_X MvPolynomial.isHomogeneous_X
-/

end

namespace IsHomogeneous

variable [CommSemiring R] {φ ψ : MvPolynomial σ R} {m n : ℕ}

#print MvPolynomial.IsHomogeneous.coeff_eq_zero /-
theorem coeff_eq_zero (hφ : IsHomogeneous φ n) (d : σ →₀ ℕ) (hd : ∑ i in d.support, d i ≠ n) :
    coeff d φ = 0 := by
  have aux := mt (@hφ d) hd
  classical
#align mv_polynomial.is_homogeneous.coeff_eq_zero MvPolynomial.IsHomogeneous.coeff_eq_zero
-/

#print MvPolynomial.IsHomogeneous.inj_right /-
theorem inj_right (hm : IsHomogeneous φ m) (hn : IsHomogeneous φ n) (hφ : φ ≠ 0) : m = n :=
  by
  obtain ⟨d, hd⟩ : ∃ d, coeff d φ ≠ 0 := exists_coeff_ne_zero hφ
  rw [← hm hd, ← hn hd]
#align mv_polynomial.is_homogeneous.inj_right MvPolynomial.IsHomogeneous.inj_right
-/

#print MvPolynomial.IsHomogeneous.add /-
theorem add (hφ : IsHomogeneous φ n) (hψ : IsHomogeneous ψ n) : IsHomogeneous (φ + ψ) n :=
  (homogeneousSubmodule σ R n).add_mem hφ hψ
#align mv_polynomial.is_homogeneous.add MvPolynomial.IsHomogeneous.add
-/

#print MvPolynomial.IsHomogeneous.sum /-
theorem sum {ι : Type _} (s : Finset ι) (φ : ι → MvPolynomial σ R) (n : ℕ)
    (h : ∀ i ∈ s, IsHomogeneous (φ i) n) : IsHomogeneous (∑ i in s, φ i) n :=
  (homogeneousSubmodule σ R n).sum_mem h
#align mv_polynomial.is_homogeneous.sum MvPolynomial.IsHomogeneous.sum
-/

#print MvPolynomial.IsHomogeneous.mul /-
theorem mul (hφ : IsHomogeneous φ m) (hψ : IsHomogeneous ψ n) : IsHomogeneous (φ * ψ) (m + n) :=
  homogeneousSubmodule_mul m n <| Submodule.mul_mem_mul hφ hψ
#align mv_polynomial.is_homogeneous.mul MvPolynomial.IsHomogeneous.mul
-/

#print MvPolynomial.IsHomogeneous.prod /-
theorem prod {ι : Type _} (s : Finset ι) (φ : ι → MvPolynomial σ R) (n : ι → ℕ)
    (h : ∀ i ∈ s, IsHomogeneous (φ i) (n i)) : IsHomogeneous (∏ i in s, φ i) (∑ i in s, n i) := by
  classical
#align mv_polynomial.is_homogeneous.prod MvPolynomial.IsHomogeneous.prod
-/

#print MvPolynomial.IsHomogeneous.totalDegree /-
theorem totalDegree (hφ : IsHomogeneous φ n) (h : φ ≠ 0) : totalDegree φ = n :=
  by
  rw [total_degree]
  apply le_antisymm
  · apply Finset.sup_le
    intro d hd
    rw [mem_support_iff] at hd 
    rw [Finsupp.sum, hφ hd]
  · obtain ⟨d, hd⟩ : ∃ d, coeff d φ ≠ 0 := exists_coeff_ne_zero h
    simp only [← hφ hd, Finsupp.sum]
    replace hd := finsupp.mem_support_iff.mpr hd
    exact Finset.le_sup hd
#align mv_polynomial.is_homogeneous.total_degree MvPolynomial.IsHomogeneous.totalDegree
-/

#print MvPolynomial.IsHomogeneous.HomogeneousSubmodule.gcommSemiring /-
/--
The homogeneous submodules form a graded ring. This instance is used by `direct_sum.comm_semiring`
and `direct_sum.algebra`. -/
instance HomogeneousSubmodule.gcommSemiring : SetLike.GradedMonoid (homogeneousSubmodule σ R)
    where
  one_mem := isHomogeneous_one σ R
  hMul_mem i j xi xj := IsHomogeneous.mul
#align mv_polynomial.is_homogeneous.homogeneous_submodule.gcomm_semiring MvPolynomial.IsHomogeneous.HomogeneousSubmodule.gcommSemiring
-/

open scoped DirectSum

noncomputable example : CommSemiring (⨁ i, homogeneousSubmodule σ R i) :=
  inferInstance

noncomputable example : Algebra R (⨁ i, homogeneousSubmodule σ R i) :=
  inferInstance

end IsHomogeneous

section

noncomputable section

open Finset

#print MvPolynomial.homogeneousComponent /-
/-- `homogeneous_component n φ` is the part of `φ` that is homogeneous of degree `n`.
See `sum_homogeneous_component` for the statement that `φ` is equal to the sum
of all its homogeneous components. -/
def homogeneousComponent [CommSemiring R] (n : ℕ) : MvPolynomial σ R →ₗ[R] MvPolynomial σ R :=
  (Submodule.subtype _).comp <| Finsupp.restrictDom _ _ {d | ∑ i in d.support, d i = n}
#align mv_polynomial.homogeneous_component MvPolynomial.homogeneousComponent
-/

section HomogeneousComponent

open Finset

variable [CommSemiring R] (n : ℕ) (φ ψ : MvPolynomial σ R)

#print MvPolynomial.coeff_homogeneousComponent /-
theorem coeff_homogeneousComponent (d : σ →₀ ℕ) :
    coeff d (homogeneousComponent n φ) = if ∑ i in d.support, d i = n then coeff d φ else 0 := by
  convert Finsupp.filter_apply (fun d : σ →₀ ℕ => ∑ i in d.support, d i = n) φ d
#align mv_polynomial.coeff_homogeneous_component MvPolynomial.coeff_homogeneousComponent
-/

#print MvPolynomial.homogeneousComponent_apply /-
theorem homogeneousComponent_apply :
    homogeneousComponent n φ =
      ∑ d in φ.support.filterₓ fun d => ∑ i in d.support, d i = n, monomial d (coeff d φ) :=
  by convert Finsupp.filter_eq_sum (fun d : σ →₀ ℕ => ∑ i in d.support, d i = n) φ
#align mv_polynomial.homogeneous_component_apply MvPolynomial.homogeneousComponent_apply
-/

#print MvPolynomial.homogeneousComponent_isHomogeneous /-
theorem homogeneousComponent_isHomogeneous : (homogeneousComponent n φ).Homogeneous n :=
  by
  intro d hd
  contrapose! hd
  rw [coeff_homogeneous_component, if_neg hd]
#align mv_polynomial.homogeneous_component_is_homogeneous MvPolynomial.homogeneousComponent_isHomogeneous
-/

#print MvPolynomial.homogeneousComponent_zero /-
@[simp]
theorem homogeneousComponent_zero : homogeneousComponent 0 φ = C (coeff 0 φ) :=
  by
  ext1 d
  rcases em (d = 0) with (rfl | hd)
  · classical
  · rw [coeff_homogeneous_component, if_neg, coeff_C, if_neg (Ne.symm hd)]
    simp only [Finsupp.ext_iff, Finsupp.zero_apply] at hd 
    simp [hd]
#align mv_polynomial.homogeneous_component_zero MvPolynomial.homogeneousComponent_zero
-/

#print MvPolynomial.homogeneousComponent_C_mul /-
@[simp]
theorem homogeneousComponent_C_mul (n : ℕ) (r : R) :
    homogeneousComponent n (C r * φ) = C r * homogeneousComponent n φ := by
  simp only [C_mul', LinearMap.map_smul]
#align mv_polynomial.homogeneous_component_C_mul MvPolynomial.homogeneousComponent_C_mul
-/

#print MvPolynomial.homogeneousComponent_eq_zero' /-
theorem homogeneousComponent_eq_zero'
    (h : ∀ d : σ →₀ ℕ, d ∈ φ.support → ∑ i in d.support, d i ≠ n) : homogeneousComponent n φ = 0 :=
  by
  rw [homogeneous_component_apply, sum_eq_zero]
  intro d hd; rw [mem_filter] at hd 
  exfalso; exact h _ hd.1 hd.2
#align mv_polynomial.homogeneous_component_eq_zero' MvPolynomial.homogeneousComponent_eq_zero'
-/

#print MvPolynomial.homogeneousComponent_eq_zero /-
theorem homogeneousComponent_eq_zero (h : φ.totalDegree < n) : homogeneousComponent n φ = 0 :=
  by
  apply homogeneous_component_eq_zero'
  rw [total_degree, Finset.sup_lt_iff] at h 
  · intro d hd; exact ne_of_lt (h d hd)
  · exact lt_of_le_of_lt (Nat.zero_le _) h
#align mv_polynomial.homogeneous_component_eq_zero MvPolynomial.homogeneousComponent_eq_zero
-/

#print MvPolynomial.sum_homogeneousComponent /-
theorem sum_homogeneousComponent : ∑ i in range (φ.totalDegree + 1), homogeneousComponent i φ = φ :=
  by
  ext1 d
  suffices φ.total_degree < d.support.sum d → 0 = coeff d φ by
    simpa [coeff_sum, coeff_homogeneous_component]
  exact fun h => (coeff_eq_zero_of_total_degree_lt h).symm
#align mv_polynomial.sum_homogeneous_component MvPolynomial.sum_homogeneousComponent
-/

#print MvPolynomial.homogeneousComponent_homogeneous_polynomial /-
theorem homogeneousComponent_homogeneous_polynomial (m n : ℕ) (p : MvPolynomial σ R)
    (h : p ∈ homogeneousSubmodule σ R n) : homogeneousComponent m p = if m = n then p else 0 :=
  by
  simp only [mem_homogeneous_submodule] at h 
  ext x
  rw [coeff_homogeneous_component]
  by_cases zero_coeff : coeff x p = 0
  · split_ifs
    all_goals simp only [zero_coeff, coeff_zero]
  · rw [h zero_coeff]
    simp only [show n = m ↔ m = n from eq_comm]
    split_ifs with h1
    · rfl
    · simp only [coeff_zero]
#align mv_polynomial.homogeneous_component_homogeneous_polynomial MvPolynomial.homogeneousComponent_homogeneous_polynomial
-/

end HomogeneousComponent

end

end MvPolynomial

