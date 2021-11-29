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


noncomputable theory

namespace Polynomial.Chebyshev

open Polynomial

variable(R S : Type _)[CommRingₓ R][CommRingₓ S]

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

variable{R S}

theorem map_T (f : R →+* S) : ∀ (n : ℕ), map f (T R n) = T S n
| 0 =>
  by 
    simp only [T_zero, map_one]
| 1 =>
  by 
    simp only [T_one, map_X]
| n+2 =>
  by 
    simp only [T_add_two, map_mul, map_sub, map_X, bit0, map_add, map_one]
    rw [map_T (n+1), map_T n]

variable(R S)

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

theorem U_eq_X_mul_U_add_T : ∀ (n : ℕ), U R (n+1) = (X*U R n)+T R (n+1)
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

theorem T_eq_X_mul_T_sub_pol_U : ∀ (n : ℕ), T R (n+2) = (X*T R (n+1)) - (1 - X ^ 2)*U R n
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

variable{R S}

@[simp]
theorem map_U (f : R →+* S) : ∀ (n : ℕ), map f (U R n) = U S n
| 0 =>
  by 
    simp only [U_zero, map_one]
| 1 =>
  by 
    simp only [U_one, map_X, map_mul, map_add, map_one]
    change (map f (1+1)*X) = 2*X 
    simpa only [map_add, map_one]
| n+2 =>
  by 
    simp only [U_add_two, map_mul, map_sub, map_X, bit0, map_add, map_one]
    rw [map_U (n+1), map_U n]

theorem T_derivative_eq_U : ∀ (n : ℕ), derivative (T R (n+1)) = (n+1)*U R n
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
    _ = («expr↑ » (n+2)+1)*U R (n+2) :=
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
    

-- error in RingTheory.Polynomial.Chebyshev: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem add_one_mul_T_eq_poly_in_U
(n : exprℕ()) : «expr = »(«expr * »(«expr + »((n : polynomial R), 1), T R «expr + »(n, 1)), «expr - »(«expr * »(X, U R n), «expr * »(«expr - »(1, «expr ^ »(X, 2)), derivative (U R n)))) :=
begin
  have [ident h] [":", expr «expr = »(derivative (T R «expr + »(n, 2)), «expr - »(«expr + »(«expr + »(«expr - »(U R «expr + »(n, 1), «expr * »(X, U R n)), «expr * »(X, derivative (T R «expr + »(n, 1)))), «expr * »(«expr * »(2, X), U R n)), «expr * »(«expr - »(1, «expr ^ »(X, 2)), derivative (U R n))))] [],
  { conv_lhs [] [] { rw [expr T_eq_X_mul_T_sub_pol_U] },
    simp [] [] ["only"] ["[", expr derivative_sub, ",", expr derivative_mul, ",", expr derivative_X, ",", expr derivative_one, ",", expr derivative_X_pow, ",", expr one_mul, ",", expr T_derivative_eq_U, "]"] [] [],
    rw ["[", expr T_eq_U_sub_X_mul_U, ",", expr nat.cast_bit0, ",", expr nat.cast_one, "]"] [],
    ring [] },
  calc
    «expr = »(«expr * »(«expr + »((n : polynomial R), 1), T R «expr + »(n, 1)), «expr - »(«expr - »(«expr * »(«expr + »(«expr + »((n : polynomial R), 1), 1), «expr + »(«expr * »(X, U R n), T R «expr + »(n, 1))), «expr * »(X, «expr * »(«expr + »(n, 1), U R n))), «expr + »(«expr * »(X, U R n), T R «expr + »(n, 1)))) : by ring []
    «expr = »(..., «expr - »(«expr - »(derivative (T R «expr + »(n, 2)), «expr * »(X, derivative (T R «expr + »(n, 1)))), U R «expr + »(n, 1))) : by rw ["[", "<-", expr U_eq_X_mul_U_add_T, ",", "<-", expr T_derivative_eq_U, ",", "<-", expr nat.cast_one, ",", "<-", expr nat.cast_add, ",", expr nat.cast_one, ",", "<-", expr T_derivative_eq_U «expr + »(n, 1), "]"] []
    «expr = »(..., «expr - »(«expr - »(«expr - »(«expr + »(«expr + »(«expr - »(U R «expr + »(n, 1), «expr * »(X, U R n)), «expr * »(X, derivative (T R «expr + »(n, 1)))), «expr * »(«expr * »(2, X), U R n)), «expr * »(«expr - »(1, «expr ^ »(X, 2)), derivative (U R n))), «expr * »(X, derivative (T R «expr + »(n, 1)))), U R «expr + »(n, 1))) : by rw [expr h] []
    «expr = »(..., «expr - »(«expr * »(X, U R n), «expr * »(«expr - »(1, «expr ^ »(X, 2)), derivative (U R n)))) : by ring []
end

variable(R)

-- error in RingTheory.Polynomial.Chebyshev: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- The product of two Chebyshev polynomials is the sum of two other Chebyshev polynomials. -/
theorem mul_T : ∀
m : exprℕ(), ∀
k, «expr = »(«expr * »(«expr * »(2, T R m), T R «expr + »(m, k)), «expr + »(T R «expr + »(«expr * »(2, m), k), T R k))
| 0 := by simp [] [] [] ["[", expr two_mul, ",", expr add_mul, "]"] [] []
| 1 := by simp [] [] [] ["[", expr add_comm, "]"] [] []
| «expr + »(m, 2) := begin
  intros [ident k],
  suffices [] [":", expr «expr = »(«expr * »(«expr * »(2, T R «expr + »(m, 2)), T R «expr + »(«expr + »(m, k), 2)), «expr + »(T R «expr + »(«expr + »(«expr * »(2, m), k), 4), T R k))],
  { have [ident h_nat₁] [":", expr «expr = »(«expr + »(«expr * »(2, «expr + »(m, 2)), k), «expr + »(«expr + »(«expr * »(2, m), k), 4))] [":=", expr by ring []],
    have [ident h_nat₂] [":", expr «expr = »(«expr + »(«expr + »(m, 2), k), «expr + »(«expr + »(m, k), 2))] [":=", expr by simp [] [] [] ["[", expr add_comm, ",", expr add_assoc, "]"] [] []],
    simpa [] [] [] ["[", expr h_nat₁, ",", expr h_nat₂, "]"] [] ["using", expr this] },
  have [ident H₁] [":", expr «expr = »(«expr * »(«expr * »(2, T R «expr + »(m, 1)), T R «expr + »(«expr + »(m, k), 2)), «expr + »(T R «expr + »(«expr + »(«expr * »(2, m), k), 3), T R «expr + »(k, 1)))] [],
  { have [ident h_nat₁] [":", expr «expr = »(«expr + »(«expr + »(m, 1), «expr + »(k, 1)), «expr + »(«expr + »(m, k), 2))] [":=", expr by ring []],
    have [ident h_nat₂] [":", expr «expr = »(«expr + »(«expr * »(2, «expr + »(m, 1)), «expr + »(k, 1)), «expr + »(«expr + »(«expr * »(2, m), k), 3))] [":=", expr by ring []],
    simpa [] [] [] ["[", expr h_nat₁, ",", expr h_nat₂, "]"] [] ["using", expr mul_T «expr + »(m, 1) «expr + »(k, 1)] },
  have [ident H₂] [":", expr «expr = »(«expr * »(«expr * »(2, T R m), T R «expr + »(«expr + »(m, k), 2)), «expr + »(T R «expr + »(«expr + »(«expr * »(2, m), k), 2), T R «expr + »(k, 2)))] [],
  { have [ident h_nat₁] [":", expr «expr = »(«expr + »(«expr * »(2, m), «expr + »(k, 2)), «expr + »(«expr + »(«expr * »(2, m), k), 2))] [":=", expr by simp [] [] [] ["[", expr add_assoc, "]"] [] []],
    have [ident h_nat₂] [":", expr «expr = »(«expr + »(m, «expr + »(k, 2)), «expr + »(«expr + »(m, k), 2))] [":=", expr by simp [] [] [] ["[", expr add_assoc, "]"] [] []],
    simpa [] [] [] ["[", expr h_nat₁, ",", expr h_nat₂, "]"] [] ["using", expr mul_T m «expr + »(k, 2)] },
  have [ident h₁] [] [":=", expr T_add_two R m],
  have [ident h₂] [] [":=", expr T_add_two R «expr + »(«expr + »(«expr * »(2, m), k), 2)],
  have [ident h₃] [] [":=", expr T_add_two R k],
  apply_fun [expr λ p, «expr * »(«expr * »(2, X), p)] ["at", ident H₁] [],
  apply_fun [expr λ p, «expr * »(«expr * »(2, T R «expr + »(«expr + »(m, k), 2)), p)] ["at", ident h₁] [],
  have [ident e₁] [] [":=", expr congr (congr_arg has_add.add H₁) h₁],
  have [ident e₂] [] [":=", expr congr (congr_arg has_sub.sub e₁) H₂],
  have [ident e₃] [] [":=", expr congr (congr_arg has_sub.sub e₂) h₂],
  have [ident e₄] [] [":=", expr congr (congr_arg has_sub.sub e₃) h₃],
  rw ["<-", expr sub_eq_zero] ["at", ident e₄, "⊢"],
  rw ["<-", expr e₄] [],
  ring []
end

-- error in RingTheory.Polynomial.Chebyshev: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- The `(m * n)`-th Chebyshev polynomial is the composition of the `m`-th and `n`-th -/
theorem T_mul : ∀ m : exprℕ(), ∀ n : exprℕ(), «expr = »(T R «expr * »(m, n), (T R m).comp (T R n))
| 0 := by simp [] [] [] [] [] []
| 1 := by simp [] [] [] [] [] []
| «expr + »(m, 2) := begin
  intros [ident n],
  have [] [":", expr «expr = »(«expr * »(«expr * »(2, T R n), T R «expr * »(«expr + »(m, 1), n)), «expr + »(T R «expr * »(«expr + »(m, 2), n), T R «expr * »(m, n)))] [],
  { convert [] [expr mul_T R n «expr * »(m, n)] []; ring [] },
  simp [] [] [] ["[", expr this, ",", expr T_mul m, ",", "<-", expr T_mul «expr + »(m, 1), "]"] [] []
end

end Polynomial.Chebyshev

