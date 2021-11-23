import Mathbin.Analysis.Complex.Basic 
import Mathbin.RingTheory.Polynomial.Chebyshev 
import Mathbin.Data.Complex.Exponential

/-!
# Multiple angle formulas in terms of Chebyshev polynomials

* `polynomial.chebyshev.T_complex_cos`: the `n`-th Chebyshev polynomial evaluates on `complex.cos θ`
  to the value `complex.cos (n * θ)`.
-/


namespace Polynomial.Chebyshev

open Polynomial Complex

-- error in Analysis.SpecialFunctions.Trigonometric.Chebyshev: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- The `n`-th Chebyshev polynomial of the first kind evaluates on `cos θ` to the
value `cos (n * θ)`. -/
theorem T_complex_cos (θ : exprℂ()) : ∀ n, «expr = »((T exprℂ() n).eval (cos θ), cos «expr * »(n, θ))
| 0 := by simp [] [] ["only"] ["[", expr T_zero, ",", expr eval_one, ",", expr nat.cast_zero, ",", expr zero_mul, ",", expr cos_zero, "]"] [] []
| 1 := by simp [] [] ["only"] ["[", expr eval_X, ",", expr one_mul, ",", expr T_one, ",", expr nat.cast_one, "]"] [] []
| «expr + »(n, 2) := begin
  simp [] [] ["only"] ["[", expr eval_X, ",", expr eval_one, ",", expr T_add_two, ",", expr eval_sub, ",", expr eval_bit0, ",", expr nat.cast_succ, ",", expr eval_mul, "]"] [] [],
  rw ["[", expr T_complex_cos «expr + »(n, 1), ",", expr T_complex_cos n, "]"] [],
  have [ident aux] [":", expr «expr = »(«expr * »(sin θ, sin θ), «expr - »(1, «expr * »(cos θ, cos θ)))] [],
  { rw ["<-", expr sin_sq_add_cos_sq θ] [],
    ring [] },
  simp [] [] ["only"] ["[", expr nat.cast_add, ",", expr nat.cast_one, ",", expr add_mul, ",", expr cos_add, ",", expr one_mul, ",", expr sin_add, ",", expr mul_assoc, ",", expr aux, "]"] [] [],
  ring []
end

/-- `cos (n * θ)` is equal to the `n`-th Chebyshev polynomial of the first kind evaluated
on `cos θ`. -/
theorem cos_nat_mul (n : ℕ) (θ : ℂ) : cos (n*θ) = (T ℂ n).eval (cos θ) :=
  (T_complex_cos θ n).symm

/-- The `n`-th Chebyshev polynomial of the second kind evaluates on `cos θ` to the
value `sin ((n+1) * θ) / sin θ`. -/
theorem U_complex_cos (θ : ℂ) (n : ℕ) : ((U ℂ n).eval (cos θ)*sin θ) = sin ((n+1)*θ) :=
  by 
    induction' n with d hd
    ·
      simp only [U_zero, Nat.cast_zero, eval_one, mul_oneₓ, zero_addₓ, one_mulₓ]
    ·
      rw [U_eq_X_mul_U_add_T]
      simp only [eval_add, eval_mul, eval_X, T_complex_cos, add_mulₓ, mul_assocₓ, hd, one_mulₓ]
      convRHS => rw [sin_add, mul_commₓ]
      pushCast 
      simp only [add_mulₓ, one_mulₓ]

/-- `sin ((n + 1) * θ)` is equal to `sin θ` multiplied with the `n`-th Chebyshev polynomial of the
second kind evaluated on `cos θ`. -/
theorem sin_nat_succ_mul (n : ℕ) (θ : ℂ) : sin ((n+1)*θ) = (U ℂ n).eval (cos θ)*sin θ :=
  (U_complex_cos θ n).symm

end Polynomial.Chebyshev

