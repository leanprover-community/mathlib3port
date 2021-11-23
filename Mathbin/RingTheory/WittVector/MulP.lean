import Mathbin.RingTheory.WittVector.IsPoly

/-!
## Multiplication by `n` in the ring of Witt vectors

In this file we show that multiplication by `n` in the ring of Witt vectors
is a polynomial function. We then use this fact to show that the composition of Frobenius
and Verschiebung is equal to multiplication by `p`.

### Main declarations

* `mul_n_is_poly`: multiplication by `n` is a polynomial function

## References

* [Hazewinkel, *Witt Vectors*][Haze09]

* [Commelin and Lewis, *Formalizing the Ring of Witt Vectors*][CL21]
-/


namespace WittVector

variable{p : ℕ}{R : Type _}[hp : Fact p.prime][CommRingₓ R]

local notation "𝕎" => WittVector p

open MvPolynomial

noncomputable theory

include hp

variable(p)

-- error in RingTheory.WittVector.MulP: ././Mathport/Syntax/Translate/Basic.lean:558:61: unsupported notation `«expr![ , ]»
/-- `witt_mul_n p n` is the family of polynomials that computes
the coefficients of `x * n` in terms of the coefficients of the Witt vector `x`. -/
noncomputable
def witt_mul_n : exprℕ() → exprℕ() → mv_polynomial exprℕ() exprℤ()
| 0 := 0
| «expr + »(n, 1) := λ k, bind₁ «expr $ »(function.uncurry, «expr![ , ]»([witt_mul_n n, X])) (witt_add p k)

variable{p}

theorem mul_n_coeff (n : ℕ) (x : 𝕎 R) (k : ℕ) : (x*n).coeff k = aeval x.coeff (witt_mul_n p n k) :=
  by 
    induction' n with n ih generalizing k
    ·
      simp only [Nat.nat_zero_eq_zero, Nat.cast_zero, mul_zero, zero_coeff, witt_mul_n, AlgHom.map_zero, Pi.zero_apply]
    ·
      rw [witt_mul_n, Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one, mul_addₓ, mul_oneₓ, aeval_bind₁, add_coeff]
      apply eval₂_hom_congr (RingHom.ext_int _ _) _ rfl 
      ext1 ⟨b, i⟩
      finCases b
      ·
        simp only [Function.uncurry, Matrix.cons_val_zero, ih]
      ·
        simp only [Function.uncurry, Matrix.cons_val_one, Matrix.head_cons, aeval_X]

variable(p)

/-- Multiplication by `n` is a polynomial function. -/
@[isPoly]
theorem mul_n_is_poly (n : ℕ) :
  is_poly p
    fun R _Rcr x =>
      by 
        exact x*n :=
  ⟨⟨witt_mul_n p n,
      fun R _Rcr x =>
        by 
          funext k 
          exact mul_n_coeff n x k⟩⟩

@[simp]
theorem bind₁_witt_mul_n_witt_polynomial (n k : ℕ) :
  bind₁ (witt_mul_n p n) (wittPolynomial p ℤ k) = n*wittPolynomial p ℤ k :=
  by 
    induction' n with n ih
    ·
      simp only [witt_mul_n, Nat.cast_zero, zero_mul, bind₁_zero_witt_polynomial]
    ·
      rw [witt_mul_n, ←bind₁_bind₁, witt_add, witt_structure_int_prop]
      simp only [AlgHom.map_add, Nat.cast_succ, bind₁_X_right]
      rw [add_mulₓ, one_mulₓ, bind₁_rename, bind₁_rename]
      simp only [ih, Function.uncurry, Function.comp, bind₁_X_left, AlgHom.id_apply, Matrix.cons_val_zero,
        Matrix.head_cons, Matrix.cons_val_one]

end WittVector

