/-
Copyright (c) 2020 Hanting Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hanting Zhang
-/
import Mathbin.FieldTheory.SplittingField
import Mathbin.RingTheory.Polynomial.Symmetric

/-!
# Vieta's Formula

The main result is `multiset.prod_X_add_C_eq_sum_esymm`, which shows that the product of
linear terms `X + λ` with `λ` in a `multiset s` is equal to a linear combination of the
symmetric functions `esymm s`.

From this, we deduce `mv_polynomial.prod_X_add_C_eq_sum_esymm` which is the equivalent formula
for the product of linear terms `X + X i` with `i` in a `fintype σ` as a linear combination
of the symmetric polynomials `esymm σ R j`.

For `R` be an integral domain (so that `p.roots` is defined for any `p : R[X]` as a multiset),
we derive `polynomial.coeff_eq_esymm_roots_of_card`, the relationship between the coefficients and
the roots of `p` for a polynomial `p` that splits (i.e. having as many roots as its degree).
-/


open BigOperators Polynomial

namespace Multiset

open Polynomial

section Semiringₓ

variable {R : Type _} [CommSemiringₓ R]

/-- A sum version of Vieta's formula for `multiset`: the product of the linear terms `X + λ` where
`λ` runs through a multiset `s` is equal to a linear combination of the symmetric functions
`esymm s` of the `λ`'s .-/
theorem prod_X_add_C_eq_sum_esymm (s : Multiset R) :
    (s.map fun r => X + c r).Prod = ∑ j in Finset.range (s.card + 1), c (s.esymm j) * X ^ (s.card - j) := by
  classical
  rw [prod_map_add, antidiagonal_eq_map_powerset, map_map, ← bind_powerset_len, Function.comp, map_bind, sum_bind,
    Finset.sum_eq_multiset_sum, Finset.range_coe, map_congr (Eq.refl _)]
  intro _ _
  rw [esymm, ← sum_hom', ← sum_map_mul_right, map_congr (Eq.refl _)]
  intro _ ht
  rw [mem_powerset_len] at ht
  simp [ht, map_const, prod_repeat, prod_hom', map_id', card_sub]

/-- Vieta's formula for the coefficients of the product of linear terms `X + λ` where `λ` runs
through a multiset `s` : the `k`th coefficient is the symmetric function `esymm (card s - k) s`. -/
theorem prod_X_add_C_coeff (s : Multiset R) {k : ℕ} (h : k ≤ s.card) :
    (s.map fun r => X + c r).Prod.coeff k = s.esymm (s.card - k) := by
  convert polynomial.ext_iff.mp (prod_X_add_C_eq_sum_esymm s) k
  simp_rw [finset_sum_coeff, coeff_C_mul_X_pow]
  rw [Finset.sum_eq_single_of_mem (s.card - k) _]
  · rw [if_pos (Nat.sub_sub_selfₓ h).symm]
    
  · intro j hj1 hj2
    suffices k ≠ card s - j by
      rw [if_neg this]
    · intro hn
      rw [hn, Nat.sub_sub_selfₓ (nat.lt_succ_iff.mp (finset.mem_range.mp hj1))] at hj2
      exact Ne.irrefl hj2
      
    
  · rw [Finset.mem_range]
    exact Nat.sub_lt_succₓ s.card k
    

end Semiringₓ

section Ringₓ

variable {R : Type _} [CommRingₓ R]

theorem esymm_neg (s : Multiset R) (k : ℕ) : (map Neg.neg s).esymm k = -1 ^ k * esymm s k := by
  rw [esymm, esymm, ← Multiset.sum_map_mul_left, Multiset.powerset_len_map, Multiset.map_map, map_congr (Eq.refl _)]
  intro x hx
  rw [(mem_powerset_len.mp hx).right.symm, ← prod_repeat, ← Multiset.map_const]
  nth_rw 2[← map_id' x]
  rw [← prod_map_mul, map_congr (Eq.refl _)]
  exact fun z _ => neg_one_mul z

theorem prod_X_sub_C_eq_sum_esymm (s : Multiset R) :
    (s.map fun t => X - c t).Prod = ∑ j in Finset.range (s.card + 1), -1 ^ j * (c (s.esymm j) * X ^ (s.card - j)) := by
  conv_lhs => congr congr ext rw [sub_eq_add_neg]rw [← map_neg C _]
  convert prod_X_add_C_eq_sum_esymm (map (fun t => -t) s) using 1
  · rwa [map_map]
    
  · simp only [esymm_neg, card_map, mul_assoc, map_mul, map_pow, map_neg, map_one]
    

theorem prod_X_sub_C_coeff (s : Multiset R) {k : ℕ} (h : k ≤ s.card) :
    (s.map fun t => X - c t).Prod.coeff k = -1 ^ (s.card - k) * s.esymm (s.card - k) := by
  conv_lhs => congr congr congr ext rw [sub_eq_add_neg]rw [← map_neg C _]
  convert prod_X_add_C_coeff (map (fun t => -t) s) _ using 1
  · rwa [map_map]
    
  · rwa [esymm_neg, card_map]
    
  · rwa [card_map]
    

/-- Vieta's formula for the coefficients and the roots of a polynomial over an integral domain
  with as many roots as its degree. -/
theorem _root_.polynomial.coeff_eq_esymm_roots_of_card [IsDomain R] {p : R[X]} (hroots : p.roots.card = p.natDegree)
    {k : ℕ} (h : k ≤ p.natDegree) :
    p.coeff k = p.leadingCoeff * -1 ^ (p.natDegree - k) * p.roots.esymm (p.natDegree - k) := by
  conv_lhs => rw [← C_leading_coeff_mul_prod_multiset_X_sub_C hroots]
  rw [coeff_C_mul, mul_assoc]
  congr
  convert p.roots.prod_X_sub_C_coeff _ using 3 <;> rw [hroots]
  exact h

/-- Vieta's formula for split polynomials over a field. -/
theorem _root_.polynomial.coeff_eq_esymm_roots_of_splits {F} [Field F] {p : F[X]} (hsplit : p.Splits (RingHom.id F))
    {k : ℕ} (h : k ≤ p.natDegree) :
    p.coeff k = p.leadingCoeff * -1 ^ (p.natDegree - k) * p.roots.esymm (p.natDegree - k) :=
  Polynomial.coeff_eq_esymm_roots_of_card (splits_iff_card_roots.1 hsplit) h

end Ringₓ

end Multiset

section MvPolynomial

open Finset Polynomial Fintype

variable (R σ : Type _) [CommSemiringₓ R] [Fintype σ]

/-- A sum version of Vieta's formula for `mv_polynomial`: viewing `X i` as variables,
the product of linear terms `λ + X i` is equal to a linear combination of
the symmetric polynomials `esymm σ R j`. -/
theorem MvPolynomial.prod_C_add_X_eq_sum_esymm :
    (∏ i : σ, X + c (MvPolynomial.x i)) = ∑ j in range (card σ + 1), c (MvPolynomial.esymm σ R j) * X ^ (card σ - j) :=
  by
  let s := finset.univ.val.map fun i : σ => MvPolynomial.x i
  rw [(_ : card σ = s.card)]
  · simp_rw [MvPolynomial.EsymmEqMultiset.esymm σ R _, Finset.prod_eq_multiset_prod]
    convert Multiset.prod_X_add_C_eq_sum_esymm s
    rwa [Multiset.map_map]
    
  · rw [Multiset.card_map]
    exact rfl
    

theorem MvPolynomial.prod_X_add_C_coeff (k : ℕ) (h : k ≤ card σ) :
    (∏ i : σ, X + c (MvPolynomial.x i)).coeff k = MvPolynomial.esymm σ R (card σ - k) := by
  let s := finset.univ.val.map fun i => (MvPolynomial.x i : MvPolynomial σ R)
  rw [(_ : card σ = s.card)] at h⊢
  · rw [MvPolynomial.EsymmEqMultiset.esymm σ R (s.card - k), Finset.prod_eq_multiset_prod]
    convert Multiset.prod_X_add_C_coeff s h
    rwa [Multiset.map_map]
    
  repeat'
    rw [Multiset.card_map]
    exact rfl

end MvPolynomial

