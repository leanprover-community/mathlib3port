import Mathbin.Data.Polynomial.Derivative 
import Mathbin.Tactic.Ring

/-!
# Chebyshev polynomials

The Chebyshev polynomials are two families of polynomials indexed by `ℕ`,
with integral coefficients.

## Main definitions

* `polynomial.chebyshev.T`: the Chebyshev polynomials of the first kind.
* `polynomial.chebyshev.U`: the Chebyshev polynomials of the second kind.

## Main statements

* The formal derivative of the Chebyshev polynomials of the first kind is a scalar multiple of the
  Chebyshev polynomials of the second kind.
* `polynomial.chebyshev.mul_T`, the product of the `m`-th and `(m + k)`-th Chebyshev polynomials of
  the first kind is the sum of the `(2 * m + k)`-th and `k`-th Chebyshev polynomials of the first
  kind.
* `polynomial.chebyshev.T_mul`, the `(m * n)`-th Chebyshev polynomial of the first kind is the
  composition of the `m`-th and `n`-th Chebyshev polynomials of the first kind.

## Implementation details

Since Chebyshev polynomials have interesting behaviour over the complex numbers and modulo `p`,
we define them to have coefficients in an arbitrary commutative ring, even though
technically `ℤ` would suffice.
The benefit of allowing arbitrary coefficient rings, is that the statements afterwards are clean,
and do not have `map (int.cast_ring_hom R)` interfering all the time.

## References

[Lionel Ponton, _Roots of the Chebyshev polynomials: A purely algebraic approach_]
[ponton2020chebyshev]

## TODO

* Redefine and/or relate the definition of Chebyshev polynomials to `linear_recurrence`.
* Add explicit formula involving square roots for Chebyshev polynomials
* Compute zeroes and extrema of Chebyshev polynomials.
* Prove that the roots of the Chebyshev polynomials (except 0) are irrational.
* Prove minimax properties of Chebyshev polynomials.
-/


noncomputable section 

namespace Polynomial.Chebyshev

open Polynomial

variable (R S : Type _) [CommRingₓ R] [CommRingₓ S]

/-- `T n` is the `n`-th Chebyshev polynomial of the first kind -/
noncomputable def T : ℕ → Polynomial R
| 0 => 1
| 1 => X
| n+2 => ((2*X)*T (n+1)) - T n

@[simp]
theorem T_zero : T R 0 = 1 :=
  rfl

@[simp]
theorem T_one : T R 1 = X :=
  rfl

theorem T_two : T R 2 = (2*X ^ 2) - 1 :=
  by 
    simp only [T, sub_left_inj, sq, mul_assocₓ]

@[simp]
theorem T_add_two (n : ℕ) : T R (n+2) = ((2*X)*T R (n+1)) - T R n :=
  by 
    rw [T]

theorem T_of_two_le (n : ℕ) (h : 2 ≤ n) : T R n = ((2*X)*T R (n - 1)) - T R (n - 2) :=
  by 
    obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le h 
    rw [add_commₓ]
    exact T_add_two R n

variable {R S}

theorem map_T (f : R →+* S) : ∀ n : ℕ, map f (T R n) = T S n
| 0 =>
  by 
    simp only [T_zero, Polynomial.map_one]
| 1 =>
  by 
    simp only [T_one, map_X]
| n+2 =>
  by 
    simp only [T_add_two, Polynomial.map_mul, Polynomial.map_sub, map_X, bit0, Polynomial.map_add, Polynomial.map_one]
    rw [map_T (n+1), map_T n]

variable (R S)

/-- `U n` is the `n`-th Chebyshev polynomial of the second kind -/
noncomputable def U : ℕ → Polynomial R
| 0 => 1
| 1 => 2*X
| n+2 => ((2*X)*U (n+1)) - U n

@[simp]
theorem U_zero : U R 0 = 1 :=
  rfl

@[simp]
theorem U_one : U R 1 = 2*X :=
  rfl

theorem U_two : U R 2 = (4*X ^ 2) - 1 :=
  by 
    simp only [U]
    ring

@[simp]
theorem U_add_two (n : ℕ) : U R (n+2) = ((2*X)*U R (n+1)) - U R n :=
  by 
    rw [U]

theorem U_of_two_le (n : ℕ) (h : 2 ≤ n) : U R n = ((2*X)*U R (n - 1)) - U R (n - 2) :=
  by 
    obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le h 
    rw [add_commₓ]
    exact U_add_two R n

theorem U_eq_X_mul_U_add_T : ∀ n : ℕ, U R (n+1) = (X*U R n)+T R (n+1)
| 0 =>
  by 
    simp only [U_zero, U_one, T_one]
    ring
| 1 =>
  by 
    simp only [U_one, T_two, U_two]
    ring
| n+2 =>
  calc U R ((n+2)+1) = ((2*X)*(X*U R (n+1))+T R (n+2)) - (X*U R n)+T R (n+1) :=
    by 
      simp only [U_add_two, U_eq_X_mul_U_add_T n, U_eq_X_mul_U_add_T (n+1)]
    _ = (X*((2*X)*U R (n+1)) - U R n)+((2*X)*T R (n+2)) - T R (n+1) :=
    by 
      ring 
    _ = (X*U R (n+2))+T R ((n+2)+1) :=
    by 
      simp only [U_add_two, T_add_two]
    

theorem T_eq_U_sub_X_mul_U (n : ℕ) : T R (n+1) = U R (n+1) - X*U R n :=
  by 
    rw [U_eq_X_mul_U_add_T, add_commₓ (X*U R n), add_sub_cancel]

theorem T_eq_X_mul_T_sub_pol_U : ∀ n : ℕ, T R (n+2) = (X*T R (n+1)) - (1 - X ^ 2)*U R n
| 0 =>
  by 
    simp only [T_one, T_two, U_zero]
    ring
| 1 =>
  by 
    simp only [T_add_two, T_zero, T_add_two, U_one, T_one]
    ring
| n+2 =>
  calc T R ((n+2)+2) = ((2*X)*T R ((n+2)+1)) - T R (n+2) := T_add_two _ _ 
    _ = ((2*X)*(X*T R (n+2)) - (1 - X ^ 2)*U R (n+1)) - ((X*T R (n+1)) - (1 - X ^ 2)*U R n) :=
    by 
      simp only [T_eq_X_mul_T_sub_pol_U]
    _ = (X*((2*X)*T R (n+2)) - T R (n+1)) - (1 - X ^ 2)*((2*X)*U R (n+1)) - U R n :=
    by 
      ring 
    _ = (X*T R ((n+2)+1)) - (1 - X ^ 2)*U R (n+2) :=
    by 
      rw [T_add_two _ (n+1), U_add_two]
    

theorem one_sub_X_sq_mul_U_eq_pol_in_T (n : ℕ) : ((1 - X ^ 2)*U R n) = (X*T R (n+1)) - T R (n+2) :=
  by 
    rw [T_eq_X_mul_T_sub_pol_U, ←sub_add, sub_self, zero_addₓ]

variable {R S}

@[simp]
theorem map_U (f : R →+* S) : ∀ n : ℕ, map f (U R n) = U S n
| 0 =>
  by 
    simp only [U_zero, Polynomial.map_one]
| 1 =>
  by 
    simp only [U_one, map_X, Polynomial.map_mul, Polynomial.map_add, Polynomial.map_one]
    change (map f (1+1)*X) = 2*X 
    simpa only [Polynomial.map_add, Polynomial.map_one]
| n+2 =>
  by 
    simp only [U_add_two, Polynomial.map_mul, Polynomial.map_sub, map_X, bit0, Polynomial.map_add, Polynomial.map_one]
    rw [map_U (n+1), map_U n]

theorem T_derivative_eq_U : ∀ n : ℕ, derivative (T R (n+1)) = (n+1)*U R n
| 0 =>
  by 
    simp only [T_one, U_zero, derivative_X, Nat.cast_zero, zero_addₓ, mul_oneₓ]
| 1 =>
  by 
    simp only [T_two, U_one, derivative_sub, derivative_one, derivative_mul, derivative_X_pow, Nat.cast_one,
      Nat.cast_two]
    normNum
| n+2 =>
  calc derivative (T R ((n+2)+1)) = ((2*T R (n+2))+(2*X)*derivative (T R ((n+1)+1))) - derivative (T R (n+1)) :=
    by 
      simp only [T_add_two _ (n+1), derivative_sub, derivative_mul, derivative_X, derivative_bit0, derivative_one,
        bit0_zero, zero_mul, zero_addₓ, mul_oneₓ]
    _ = ((2*U R ((n+1)+1) - X*U R (n+1))+(2*X)*((n+1)+1)*U R (n+1)) - (n+1)*U R n :=
    by 
      rwModCast [T_derivative_eq_U, T_derivative_eq_U, T_eq_U_sub_X_mul_U]
    _ = ((n+1)*((2*X)*U R (n+1)) - U R n)+2*U R (n+2) :=
    by 
      ring 
    _ = ((n+1)*U R (n+2))+2*U R (n+2) :=
    by 
      rw [U_add_two]
    _ = ((n+2)+1)*U R (n+2) :=
    by 
      ring 
    _ = ((↑n+2)+1)*U R (n+2) :=
    by 
      normCast
    

theorem one_sub_X_sq_mul_derivative_T_eq_poly_in_T (n : ℕ) :
  ((1 - X ^ 2)*derivative (T R (n+1))) = (n+1)*T R n - X*T R (n+1) :=
  calc ((1 - X ^ 2)*derivative (T R (n+1))) = (1 - X ^ 2)*(n+1)*U R n :=
    by 
      rw [T_derivative_eq_U]
    _ = (n+1)*(1 - X ^ 2)*U R n :=
    by 
      ring 
    _ = (n+1)*(X*T R (n+1)) - (((2*X)*T R (n+1)) - T R n) :=
    by 
      rw [one_sub_X_sq_mul_U_eq_pol_in_T, T_add_two]
    _ = (n+1)*T R n - X*T R (n+1) :=
    by 
      ring
    

theorem add_one_mul_T_eq_poly_in_U (n : ℕ) :
  (((n : Polynomial R)+1)*T R (n+1)) = (X*U R n) - (1 - X ^ 2)*derivative (U R n) :=
  by 
    have h :
      derivative (T R (n+2)) =
        (((U R (n+1) - X*U R n)+X*derivative (T R (n+1)))+(2*X)*U R n) - (1 - X ^ 2)*derivative (U R n)
    ·
      convLHS => rw [T_eq_X_mul_T_sub_pol_U]
      simp only [derivative_sub, derivative_mul, derivative_X, derivative_one, derivative_X_pow, one_mulₓ,
        T_derivative_eq_U]
      rw [T_eq_U_sub_X_mul_U, Nat.cast_bit0, Nat.cast_one]
      ring 
    calc
      (((n : Polynomial R)+1)*T R (n+1)) =
        (((((n : Polynomial R)+1)+1)*(X*U R n)+T R (n+1)) - X*(n+1)*U R n) - (X*U R n)+T R (n+1) :=
      by 
        ring _ = (derivative (T R (n+2)) - X*derivative (T R (n+1))) - U R (n+1) :=
      by 
        rw [←U_eq_X_mul_U_add_T, ←T_derivative_eq_U, ←Nat.cast_one, ←Nat.cast_add, Nat.cast_one,
          ←T_derivative_eq_U
            (n+1)]_ =
        (((((U R (n+1) - X*U R n)+X*derivative (T R (n+1)))+(2*X)*U R n) - (1 - X ^ 2)*derivative (U R n)) -
            X*derivative (T R (n+1))) -
          U R (n+1) :=
      by 
        rw [h]_ = (X*U R n) - (1 - X ^ 2)*derivative (U R n) :=
      by 
        ring

variable (R)

/-- The product of two Chebyshev polynomials is the sum of two other Chebyshev polynomials. -/
theorem mul_T : ∀ m : ℕ, ∀ k, ((2*T R m)*T R (m+k)) = T R ((2*m)+k)+T R k
| 0 =>
  by 
    simp [two_mul, add_mulₓ]
| 1 =>
  by 
    simp [add_commₓ]
| m+2 =>
  by 
    intro k 
    suffices  : ((2*T R (m+2))*T R ((m+k)+2)) = T R (((2*m)+k)+4)+T R k
    ·
      have h_nat₁ : ((2*m+2)+k) = ((2*m)+k)+4 :=
        by 
          ring 
      have h_nat₂ : ((m+2)+k) = (m+k)+2 :=
        by 
          simp [add_commₓ, add_assocₓ]
      simpa [h_nat₁, h_nat₂] using this 
    have H₁ : ((2*T R (m+1))*T R ((m+k)+2)) = T R (((2*m)+k)+3)+T R (k+1)
    ·
      have h_nat₁ : ((m+1)+k+1) = (m+k)+2 :=
        by 
          ring 
      have h_nat₂ : ((2*m+1)+k+1) = ((2*m)+k)+3 :=
        by 
          ring 
      simpa [h_nat₁, h_nat₂] using mul_T (m+1) (k+1)
    have H₂ : ((2*T R m)*T R ((m+k)+2)) = T R (((2*m)+k)+2)+T R (k+2)
    ·
      have h_nat₁ : ((2*m)+k+2) = ((2*m)+k)+2 :=
        by 
          simp [add_assocₓ]
      have h_nat₂ : (m+k+2) = (m+k)+2 :=
        by 
          simp [add_assocₓ]
      simpa [h_nat₁, h_nat₂] using mul_T m (k+2)
    have h₁ := T_add_two R m 
    have h₂ := T_add_two R (((2*m)+k)+2)
    have h₃ := T_add_two R k 
    applyFun fun p => (2*X)*p  at H₁ 
    applyFun fun p => (2*T R ((m+k)+2))*p  at h₁ 
    have e₁ := congr (congr_argₓ Add.add H₁) h₁ 
    have e₂ := congr (congr_argₓ Sub.sub e₁) H₂ 
    have e₃ := congr (congr_argₓ Sub.sub e₂) h₂ 
    have e₄ := congr (congr_argₓ Sub.sub e₃) h₃ 
    rw [←sub_eq_zero] at e₄⊢
    rw [←e₄]
    ring

/-- The `(m * n)`-th Chebyshev polynomial is the composition of the `m`-th and `n`-th -/
theorem T_mul : ∀ m : ℕ, ∀ n : ℕ, T R (m*n) = (T R m).comp (T R n)
| 0 =>
  by 
    simp 
| 1 =>
  by 
    simp 
| m+2 =>
  by 
    intro n 
    have  : ((2*T R n)*T R ((m+1)*n)) = T R ((m+2)*n)+T R (m*n)
    ·
      convert mul_T R n (m*n) <;> ring 
    simp [this, T_mul m, ←T_mul (m+1)]

end Polynomial.Chebyshev

