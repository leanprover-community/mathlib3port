/-
Copyright (c) 2022 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca
-/
import Mathbin.RingTheory.EisensteinCriterion

/-!
# Eisenstein polynomials
Given an ideal `𝓟` of a commutative semiring `R`, we say that a polynomial `f : R[X]` is
*Eisenstein at `𝓟`* if `f.leading_coeff ∉ 𝓟`, `∀ n, n < f.nat_degree → f.coeff n ∈ 𝓟` and
`f.coeff 0 ∉ 𝓟 ^ 2`. In this file we gather miscellaneous results about Eisenstein polynomials.

## Main definitions
* `polynomial.is_eisenstein_at f 𝓟` : the property of being Eisenstein at `𝓟`.

## Main results
* `polynomial.is_eisenstein_at.irreducible` : if a primitive `f` satisfies `f.is_eisenstein_at 𝓟`,
  where `𝓟.is_prime`, then `f` is irreducible.

## Implementation details
We also define a notion `is_weakly_eisenstein_at` requiring only that
`∀ n < f.nat_degree → f.coeff n ∈ 𝓟`. This makes certain results slightly more general and it is
useful since it is sometimes better behaved (for example it is stable under `polynomial.map`).

-/


universe u v

variable {R : Type u}

open Ideal Algebra Finset

open_locale BigOperators Polynomial

namespace Polynomial

/-- Given an ideal `𝓟` of a commutative semiring `R`, we say that a polynomial `f : R[X]`
is *weakly Eisenstein at `𝓟`* if `∀ n, n < f.nat_degree → f.coeff n ∈ 𝓟`. -/
@[mk_iff]
structure IsWeaklyEisensteinAt [CommSemiringₓ R] (f : R[X]) (𝓟 : Ideal R) : Prop where
  Mem : ∀ {n}, n < f.natDegree → f.coeff n ∈ 𝓟

/-- Given an ideal `𝓟` of a commutative semiring `R`, we say that a polynomial `f : R[X]`
is *Eisenstein at `𝓟`* if `f.leading_coeff ∉ 𝓟`, `∀ n, n < f.nat_degree → f.coeff n ∈ 𝓟` and
`f.coeff 0 ∉ 𝓟 ^ 2`. -/
@[mk_iff]
structure IsEisensteinAt [CommSemiringₓ R] (f : R[X]) (𝓟 : Ideal R) : Prop where
  leading : f.leadingCoeff ∉ 𝓟
  Mem : ∀ {n}, n < f.natDegree → f.coeff n ∈ 𝓟
  not_mem : f.coeff 0 ∉ 𝓟 ^ 2

namespace IsWeaklyEisensteinAt

section CommSemiringₓ

variable [CommSemiringₓ R] {𝓟 : Ideal R} {f : R[X]} (hf : f.IsWeaklyEisensteinAt 𝓟)

include hf

theorem map {A : Type v} [CommRingₓ A] (φ : R →+* A) : (f.map φ).IsWeaklyEisensteinAt (𝓟.map φ) := by
  refine' (is_weakly_eisenstein_at_iff _ _).2 fun n hn => _
  rw [coeff_map]
  exact mem_map_of_mem _ (hf.mem (lt_of_lt_of_leₓ hn (nat_degree_map_le _ _)))

end CommSemiringₓ

section CommRingₓ

variable [CommRingₓ R] {𝓟 : Ideal R} {f : R[X]} (hf : f.IsWeaklyEisensteinAt 𝓟)

variable {S : Type v} [CommRingₓ S] [Algebra R S]

section Principal

variable {p : R}

-- mathport name: «exprP»
local notation "P" => Submodule.span R {p}

theorem exists_mem_adjoin_mul_eq_pow_nat_degree {x : S} (hx : aeval x f = 0) (hmo : f.Monic)
    (hf : f.IsWeaklyEisensteinAt P) :
    ∃ y ∈ adjoin R ({x} : Set S), (algebraMap R S) p * y = x ^ (f.map (algebraMap R S)).natDegree := by
  rw [aeval_def, Polynomial.eval₂_eq_eval_map, eval_eq_finset_sum, range_add_one, sum_insert not_mem_range_self,
    sum_range, (monic_map (algebraMap R S) hmo).coeff_nat_degree, one_mulₓ] at hx
  replace hx := eq_neg_of_add_eq_zero hx
  have : ∀, ∀ n < f.nat_degree, ∀, p ∣ f.coeff n := by
    intro n hn
    refine'
      mem_span_singleton.1
        (by
          simpa using hf.mem hn)
  choose! φ hφ using this
  conv_rhs at hx =>
    congr congr skip ext
      rw [Finₓ.coe_eq_val, coeff_map, hφ i.1 (lt_of_lt_of_leₓ i.2 (nat_degree_map_le _ _)), RingHom.map_mul, mul_assoc]
  rw [hx, ← mul_sum, neg_eq_neg_one_mul, ← mul_assoc (-1 : S), mul_comm (-1 : S), mul_assoc]
  refine' ⟨-1 * ∑ i : Finₓ (f.map (algebraMap R S)).natDegree, (algebraMap R S) (φ i.1) * x ^ i.1, _, rfl⟩
  exact
    Subalgebra.mul_mem _ (Subalgebra.neg_mem _ (Subalgebra.one_mem _))
      (Subalgebra.sum_mem _ fun i hi =>
        Subalgebra.mul_mem _ (Subalgebra.algebra_map_mem _ _)
          (Subalgebra.pow_mem _ (subset_adjoin (Set.mem_singleton x)) _))

theorem exists_mem_adjoin_mul_eq_pow_nat_degree_le {x : S} (hx : aeval x f = 0) (hmo : f.Monic)
    (hf : f.IsWeaklyEisensteinAt P) :
    ∀ i, (f.map (algebraMap R S)).natDegree ≤ i → ∃ y ∈ adjoin R ({x} : Set S), (algebraMap R S) p * y = x ^ i := by
  intro i hi
  obtain ⟨k, hk⟩ := le_iff_exists_add.1 hi
  rw [hk, pow_addₓ]
  obtain ⟨y, hy, H⟩ := exists_mem_adjoin_mul_eq_pow_nat_degree hx hmo hf
  refine' ⟨y * x ^ k, _, _⟩
  · exact Subalgebra.mul_mem _ hy (Subalgebra.pow_mem _ (subset_adjoin (Set.mem_singleton x)) _)
    
  · rw [← mul_assoc _ y, H]
    

end Principal

include hf

theorem pow_nat_degree_le_of_root_of_monic_mem {x : R} (hroot : IsRoot f x) (hmo : f.Monic) :
    ∀ i, f.natDegree ≤ i → x ^ i ∈ 𝓟 := by
  intro i hi
  obtain ⟨k, hk⟩ := le_iff_exists_add.1 hi
  rw [hk, pow_addₓ]
  suffices x ^ f.nat_degree ∈ 𝓟 by
    exact mul_mem_right (x ^ k) 𝓟 this
  rw [is_root.def, eval_eq_finset_sum, Finset.range_add_one, Finset.sum_insert Finset.not_mem_range_self,
    Finset.sum_range, hmo.coeff_nat_degree, one_mulₓ] at hroot
  rw [eq_neg_of_add_eq_zero hroot, neg_mem_iff]
  refine' Submodule.sum_mem _ fun i hi => mul_mem_right _ _ (hf.mem (Finₓ.is_lt i))

theorem pow_nat_degree_le_of_aeval_zero_of_monic_mem_map {x : S} (hx : aeval x f = 0) (hmo : f.Monic) :
    ∀ i, (f.map (algebraMap R S)).natDegree ≤ i → x ^ i ∈ 𝓟.map (algebraMap R S) := by
  suffices x ^ (f.map (algebraMap R S)).natDegree ∈ 𝓟.map (algebraMap R S) by
    intro i hi
    obtain ⟨k, hk⟩ := le_iff_exists_add.1 hi
    rw [hk, pow_addₓ]
    refine' mul_mem_right _ _ this
  rw [aeval_def, eval₂_eq_eval_map, ← is_root.def] at hx
  refine' pow_nat_degree_le_of_root_of_monic_mem (hf.map _) hx (monic_map _ hmo) _ rfl.le

end CommRingₓ

end IsWeaklyEisensteinAt

namespace IsEisensteinAt

section CommSemiringₓ

variable [CommSemiringₓ R] {𝓟 : Ideal R} {f : R[X]} (hf : f.IsEisensteinAt 𝓟)

include hf

theorem is_weakly_eisenstein_at : IsWeaklyEisensteinAt f 𝓟 :=
  ⟨hf.Mem⟩

theorem coeff_mem {n : ℕ} (hn : n ≠ f.natDegree) : f.coeff n ∈ 𝓟 := by
  cases ne_iff_lt_or_gtₓ.1 hn
  · exact hf.mem h
    
  · rw [coeff_eq_zero_of_nat_degree_lt h]
    exact Ideal.zero_mem _
    

end CommSemiringₓ

section IsDomain

variable [CommRingₓ R] [IsDomain R] {𝓟 : Ideal R} {f : R[X]} (hf : f.IsEisensteinAt 𝓟)

/-- If a primitive `f` satisfies `f.is_eisenstein_at 𝓟`, where `𝓟.is_prime`, then `f` is
irreducible. -/
theorem irreducible (hprime : 𝓟.IsPrime) (hu : f.IsPrimitive) (hfd0 : 0 < f.natDegree) : Irreducible f :=
  irreducible_of_eisenstein_criterion hprime hf.leading (fun n hn => hf.Mem (coe_lt_degree.1 hn))
    (nat_degree_pos_iff_degree_pos.1 hfd0) hf.not_mem hu

end IsDomain

end IsEisensteinAt

end Polynomial

