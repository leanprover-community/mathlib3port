import Mathbin.Data.MvPolynomial.Variables
import Mathbin.Algebra.Module.Basic
import Mathbin.Tactic.Ring

/-!
# Partial derivatives of polynomials

This file defines the notion of the formal *partial derivative* of a polynomial,
the derivative with respect to a single variable.
This derivative is not connected to the notion of derivative from analysis.
It is based purely on the polynomial exponents and coefficients.

## Main declarations

* `mv_polynomial.pderiv i p` : the partial derivative of `p` with respect to `i`.

## Notation

As in other polynomial files, we typically use the notation:

+ `σ : Type*` (indexing the variables)

+ `R : Type*` `[comm_ring R]` (the coefficients)

+ `s : σ →₀ ℕ`, a function from `σ` to `ℕ` which is zero away from a finite set.
This will give rise to a monomial in `mv_polynomial σ R` which mathematicians might call `X^s`

+ `a : R`

+ `i : σ`, with corresponding monomial `X i`, often denoted `X_i` by mathematicians

+ `p : mv_polynomial σ R`

-/


noncomputable section

open_locale Classical BigOperators

open Set Function Finsupp AddMonoidAlgebra

open_locale BigOperators

universe u

variable {R : Type u}

namespace MvPolynomial

variable {σ : Type _} {a a' a₁ a₂ : R} {s : σ →₀ ℕ}

section Pderiv

variable {R} [CommSemiringₓ R]

/-- `pderiv i p` is the partial derivative of `p` with respect to `i` -/
def pderiv (i : σ) : MvPolynomial σ R →ₗ[R] MvPolynomial σ R where
  toFun := fun p => p.sum fun A B => monomial (A - single i 1) (B * A i)
  map_smul' := by
    intro c x
    rw [sum_smul_index', smul_sum]
    · dsimp
      simp_rw [← (monomial _).map_smul, smul_eq_mul, mul_assocₓ]
      
    · intro s
      simp only [monomial_zero, zero_mul]
      
  map_add' := fun f g =>
    sum_add_index
      (by
        simp only [monomial_zero, forall_const, zero_mul])
      (by
        simp only [add_mulₓ, forall_const, eq_self_iff_true, (monomial _).map_add])

@[simp]
theorem pderiv_monomial {i : σ} : pderiv i (monomial s a) = monomial (s - single i 1) (a * s i) := by
  simp only [pderiv, monomial_zero, sum_monomial_eq, zero_mul, LinearMap.coe_mk]

@[simp]
theorem pderiv_C {i : σ} : pderiv i (C a) = 0 := by
  suffices pderiv i (monomial 0 a) = 0 by
    simpa
  simp only [monomial_zero, pderiv_monomial, Nat.cast_zero, mul_zero, zero_apply]

@[simp]
theorem pderiv_one {i : σ} : pderiv i (1 : MvPolynomial σ R) = 0 :=
  pderiv_C

theorem pderiv_eq_zero_of_not_mem_vars {i : σ} {f : MvPolynomial σ R} (h : i ∉ f.vars) : pderiv i f = 0 := by
  change (pderiv i) f = 0
  rw [f.as_sum, LinearMap.map_sum]
  apply Finset.sum_eq_zero
  intro x H
  simp [mem_support_not_mem_vars_zero H h]

theorem pderiv_X [DecidableEq σ] {i j : σ} : pderiv i (X j : MvPolynomial σ R) = if i = j then 1 else 0 := by
  refine' pderiv_monomial.trans _
  rcases eq_or_ne i j with (rfl | hne)
  · simp
    
  · simp [hne, hne.symm]
    

@[simp]
theorem pderiv_X_self {i : σ} : pderiv i (X i : MvPolynomial σ R) = 1 := by
  simp [pderiv_X]

theorem pderiv_monomial_single {i : σ} {n : ℕ} :
    pderiv i (monomial (single i n) a) = monomial (single i (n - 1)) (a * n) := by
  simp

private theorem monomial_sub_single_one_add {i : σ} {s' : σ →₀ ℕ} :
    monomial (s - single i 1 + s') (a * s i * a') = monomial (s + s' - single i 1) (a * s i * a') := by
  by_cases' h : s i = 0 <;> simp [h, sub_single_one_add]

private theorem monomial_add_sub_single_one {i : σ} {s' : σ →₀ ℕ} :
    monomial (s + (s' - single i 1)) (a * (a' * s' i)) = monomial (s + s' - single i 1) (a * (a' * s' i)) := by
  by_cases' h : s' i = 0 <;> simp [h, add_sub_single_one]

theorem pderiv_monomial_mul {i : σ} {s' : σ →₀ ℕ} :
    pderiv i (monomial s a * monomial s' a') =
      pderiv i (monomial s a) * monomial s' a' + monomial s a * pderiv i (monomial s' a') :=
  by
  simp only [monomial_sub_single_one_add, monomial_add_sub_single_one, pderiv_monomial, Pi.add_apply, monomial_mul,
    Nat.cast_add, coe_add]
  rw [mul_addₓ, (monomial _).map_add, ← mul_assocₓ, mul_right_commₓ a _ a']

@[simp]
theorem pderiv_mul {i : σ} {f g : MvPolynomial σ R} : pderiv i (f * g) = pderiv i f * g + f * pderiv i g := by
  apply induction_on' f
  · apply induction_on' g
    · intro u r u' r'
      exact pderiv_monomial_mul
      
    · intro p q hp hq u r
      rw [mul_addₓ, LinearMap.map_add, hp, hq, mul_addₓ, LinearMap.map_add]
      ring
      
    
  · intro p q hp hq
    simp [add_mulₓ, hp, hq]
    ring
    

@[simp]
theorem pderiv_C_mul {f : MvPolynomial σ R} {i : σ} : pderiv i (C a * f) = C a * pderiv i f := by
  convert LinearMap.map_smul (pderiv i) a f <;> rw [C_mul']

@[simp]
theorem pderiv_pow {i : σ} {f : MvPolynomial σ R} {n : ℕ} : pderiv i (f ^ n) = n * pderiv i f * f ^ (n - 1) := by
  induction' n with n ih
  · simp
    
  · simp only [Nat.succ_sub_succ_eq_sub, Nat.cast_succ, tsub_zero, MvPolynomial.pderiv_mul, pow_succₓ, ih]
    cases n
    · simp
      
    · simp only [Nat.succ_eq_add_one, Nat.add_succ_sub_one, add_zeroₓ, Nat.cast_add, Nat.cast_one, pow_succₓ]
      ring
      
    

@[simp]
theorem pderiv_nat_cast {i : σ} {n : ℕ} : pderiv i (n : MvPolynomial σ R) = 0 := by
  induction' n with n ih
  · simp
    
  · simp [ih]
    

end Pderiv

end MvPolynomial

