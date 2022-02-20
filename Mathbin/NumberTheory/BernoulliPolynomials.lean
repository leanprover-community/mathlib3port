/-
Copyright (c) 2021 Ashvni Narayanan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ashvni Narayanan
-/
import Mathbin.Data.Polynomial.AlgebraMap
import Mathbin.Data.Nat.Choose.Cast
import Mathbin.NumberTheory.Bernoulli

/-!
# Bernoulli polynomials

The Bernoulli polynomials (defined here : https://en.wikipedia.org/wiki/Bernoulli_polynomials)
are an important tool obtained from Bernoulli numbers.

## Mathematical overview

The $n$-th Bernoulli polynomial is defined as
$$ B_n(X) = ∑_{k = 0}^n {n \choose k} (-1)^k * B_k * X^{n - k} $$
where $B_k$ is the $k$-th Bernoulli number. The Bernoulli polynomials are generating functions,
$$ t * e^{tX} / (e^t - 1) = ∑_{n = 0}^{\infty} B_n(X) * \frac{t^n}{n!} $$

## Implementation detail

Bernoulli polynomials are defined using `bernoulli`, the Bernoulli numbers.

## Main theorems

- `sum_bernoulli`: The sum of the $k^\mathrm{th}$ Bernoulli polynomial with binomial
  coefficients up to n is `(n + 1) * X^n`.
- `bernoulli_generating_function`: The Bernoulli polynomials act as generating functions
  for the exponential.

## TODO

- `bernoulli_eval_one_neg` : $$ B_n(1 - x) = (-1)^n*B_n(x) $$

-/


noncomputable section

open_locale BigOperators

open_locale Nat Polynomial

open Nat Finset

namespace Polynomial

/-- The Bernoulli polynomials are defined in terms of the negative Bernoulli numbers. -/
def bernoulli (n : ℕ) : ℚ[X] :=
  ∑ i in range (n + 1), Polynomial.monomial (n - i) (bernoulli i * choose n i)

theorem bernoulli_def (n : ℕ) :
    bernoulli n = ∑ i in range (n + 1), Polynomial.monomial i (bernoulli (n - i) * choose n i) := by
  rw [← sum_range_reflect, add_succ_sub_one, add_zeroₓ, bernoulli]
  apply sum_congr rfl
  rintro x hx
  rw [mem_range_succ_iff] at hx
  rw [choose_symm hx, tsub_tsub_cancel_of_le hx]

/-
### examples
-/
section Examples

@[simp]
theorem bernoulli_zero : bernoulli 0 = 1 := by
  simp [bernoulli]

@[simp]
theorem bernoulli_eval_zero (n : ℕ) : (bernoulli n).eval 0 = bernoulli n := by
  rw [bernoulli, Polynomial.eval_finset_sum, sum_range_succ]
  have : (∑ x : ℕ in range n, _root_.bernoulli x * n.choose x * 0 ^ (n - x)) = 0 := by
    apply sum_eq_zero fun x hx => _
    have h : 0 < n - x := tsub_pos_of_lt (mem_range.1 hx)
    simp [h]
  simp [this]

@[simp]
theorem bernoulli_eval_one (n : ℕ) : (bernoulli n).eval 1 = bernoulli' n := by
  simp only [bernoulli, Polynomial.eval_finset_sum]
  simp only [← succ_eq_add_one, sum_range_succ, mul_oneₓ, cast_one, choose_self, (_root_.bernoulli _).mul_comm,
    sum_bernoulli, one_pow, mul_oneₓ, Polynomial.eval_C, Polynomial.eval_monomial]
  by_cases' h : n = 1
  · norm_num [h]
    
  · simp [h]
    exact bernoulli_eq_bernoulli'_of_ne_one h
    

end Examples

@[simp]
theorem sum_bernoulli (n : ℕ) :
    (∑ k in range (n + 1), ((n + 1).choose k : ℚ) • bernoulli k) = Polynomial.monomial n (n + 1 : ℚ) := by
  simp_rw [bernoulli_def, Finset.smul_sum, Finset.range_eq_Ico, ← Finset.sum_Ico_Ico_comm, Finset.sum_Ico_eq_sum_range]
  simp only [cast_succ, add_tsub_cancel_left, tsub_zero, zero_addₓ, LinearMap.map_add]
  simp_rw [Polynomial.smul_monomial, mul_comm (_root_.bernoulli _) _, smul_eq_mul, ← mul_assoc]
  conv_lhs =>
    apply_congr skip conv =>
      apply_congr skip rw [← Nat.cast_mulₓ,
        choose_mul ((le_tsub_iff_left <| mem_range_le H).1 <| mem_range_le H_1) (le.intro rfl), Nat.cast_mulₓ,
        add_commₓ x x_1, add_tsub_cancel_right, mul_assoc, mul_comm, ← smul_eq_mul, ←
        Polynomial.smul_monomial]rw [← sum_smul]
  rw [sum_range_succ_comm]
  simp only [add_right_eq_selfₓ, cast_succ, mul_oneₓ, cast_one, cast_add, add_tsub_cancel_left, choose_succ_self_right,
    one_smul, _root_.bernoulli_zero, sum_singleton, zero_addₓ, LinearMap.map_add, range_one]
  apply sum_eq_zero fun x hx => _
  have f : ∀, ∀ x ∈ range n, ∀, ¬n + 1 - x = 1 := by
    rintro x H
    rw [mem_range] at H
    rw [eq_comm]
    exact ne_of_ltₓ (Nat.lt_of_lt_of_leₓ one_lt_two (le_tsub_of_add_le_left (succ_le_succ H)))
  rw [sum_bernoulli]
  have g : ite (n + 1 - x = 1) (1 : ℚ) 0 = 0 := by
    simp only [ite_eq_right_iff, one_ne_zero]
    intro h₁
    exact (f x hx) h₁
  rw [g, zero_smul]

open PowerSeries

variable {A : Type _} [CommRingₓ A] [Algebra ℚ A]

/-- The theorem that `∑ Bₙ(t)X^n/n!)(e^X-1)=Xe^{tX}`  -/
-- TODO: define exponential generating functions, and use them here
-- This name should probably be updated afterwards
theorem bernoulli_generating_function (t : A) :
    (mk fun n => aeval t ((1 / n ! : ℚ) • bernoulli n)) * (exp A - 1) = PowerSeries.x * rescale t (exp A) := by
  -- check equality of power series by checking coefficients of X^n
  ext n
  -- n = 0 case solved by `simp`
  cases n
  · simp
    
  -- n ≥ 1, the coefficients is a sum to n+2, so use `sum_range_succ` to write as
  -- last term plus sum to n+1
  rw [coeff_succ_X_mul, coeff_rescale, coeff_exp, PowerSeries.coeff_mul, nat.sum_antidiagonal_eq_sum_range_succ_mk,
    sum_range_succ]
  -- last term is zero so kill with `add_zero`
  simp only [RingHom.map_sub, tsub_self, constant_coeff_one, constant_coeff_exp, coeff_zero_eq_constant_coeff, mul_zero,
    sub_self, add_zeroₓ]
  -- Let's multiply both sides by (n+1)! (OK because it's a unit)
  set u : Units ℚ :=
    ⟨(n + 1)!, (n + 1)!⁻¹,
      mul_inv_cancel
        (by
          exact_mod_cast factorial_ne_zero (n + 1)),
      inv_mul_cancel
        (by
          exact_mod_cast factorial_ne_zero (n + 1))⟩ with
    hu
  rw [← Units.mul_right_inj (Units.map (algebraMap ℚ A).toMonoidHom u)]
  -- now tidy up unit mess and generally do trivial rearrangements
  -- to make RHS (n+1)*t^n
  rw [Units.coe_map, mul_left_commₓ, RingHom.to_monoid_hom_eq_coe, RingHom.coe_monoid_hom, ← RingHom.map_mul, hu,
    Units.coe_mk]
  change _ = t ^ n * algebraMap ℚ A (((n + 1) * n ! : ℕ) * (1 / n !))
  rw [cast_mul, mul_assoc, mul_one_div_cancel (show (n ! : ℚ) ≠ 0 from cast_ne_zero.2 (factorial_ne_zero n)), mul_oneₓ,
    mul_comm (t ^ n), ← Polynomial.aeval_monomial, cast_add, cast_one]
  -- But this is the RHS of `sum_bernoulli_poly`
  rw [← sum_bernoulli, Finset.mul_sum, AlgHom.map_sum]
  -- and now we have to prove a sum is a sum, but all the terms are equal.
  apply Finset.sum_congr rfl
  -- The rest is just trivialities, hampered by the fact that we're coercing
  -- factorials and binomial coefficients between ℕ and ℚ and A.
  intro i hi
  -- deal with coefficients of e^X-1
  simp only [Nat.cast_choose ℚ (mem_range_le hi), coeff_mk, if_neg (mem_range_sub_ne_zero hi), one_div, AlgHom.map_smul,
    PowerSeries.coeff_one, Units.coe_mk, coeff_exp, sub_zero, LinearMap.map_sub, Algebra.smul_mul_assoc,
    Algebra.smul_def, mul_right_commₓ _ ((aeval t) _), ← mul_assoc, ← RingHom.map_mul, succ_eq_add_one]
  -- finally cancel the Bernoulli polynomial and the algebra_map
  congr
  apply congr_argₓ
  rw [mul_assoc, div_eq_mul_inv, ← mul_inv₀]

end Polynomial

