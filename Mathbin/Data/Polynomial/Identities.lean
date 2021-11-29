import Mathbin.Data.Polynomial.Derivative 
import Mathbin.Tactic.RingExp

/-!
# Theory of univariate polynomials

The main def is `binom_expansion`.
-/


noncomputable theory

namespace Polynomial

universe u v w x y z

variable {R : Type u} {S : Type v} {T : Type w} {ι : Type x} {k : Type y} {A : Type z} {a b : R} {m n : ℕ}

section Identities

/--
`(x + y)^n` can be expressed as `x^n + n*x^(n-1)*y + k * y^2` for some `k` in the ring.
-/
def pow_add_expansion {R : Type _} [CommSemiringₓ R] (x y : R) :
  ∀ n : ℕ, { k // (x+y) ^ n = ((x ^ n)+(n*x ^ (n - 1))*y)+k*y ^ 2 }
| 0 =>
  ⟨0,
    by 
      simp ⟩
| 1 =>
  ⟨0,
    by 
      simp ⟩
| n+2 =>
  by 
    cases' pow_add_expansion (n+1) with z hz 
    exists ((x*z)+(n+1)*x ^ n)+z*y 
    calc ((x+y) ^ n+2) = (x+y)*(x+y) ^ n+1 :=
      by 
        ringExp _ = (x+y)*((x ^ n+1)+(«expr↑ » (n+1)*x ^ ((n+1) - 1))*y)+z*y ^ 2 :=
      by 
        rw [hz]_ = ((x ^ n+2)+(«expr↑ » (n+2)*x ^ n+1)*y)+(((x*z)+(n+1)*x ^ n)+z*y)*y ^ 2 :=
      by 
        pushCast 
        ringExp!

variable [CommRingₓ R]

private def poly_binom_aux1 (x y : R) (e : ℕ) (a : R) :
  { k : R // (a*(x+y) ^ e) = a*((x ^ e)+(e*x ^ (e - 1))*y)+k*y ^ 2 } :=
  by 
    exists (pow_add_expansion x y e).val 
    congr 
    apply (pow_add_expansion _ _ _).property

private theorem poly_binom_aux2 (f : Polynomial R) (x y : R) :
  f.eval (x+y) = f.sum fun e a => a*((x ^ e)+(e*x ^ (e - 1))*y)+(poly_binom_aux1 x y e a).val*y ^ 2 :=
  by 
    unfold eval eval₂ 
    congr with n z 
    apply (poly_binom_aux1 x y _ _).property

private theorem poly_binom_aux3 (f : Polynomial R) (x y : R) :
  f.eval (x+y) =
    ((f.sum
          fun e a =>
            a*x ^ e)+f.sum fun e a => ((a*e)*x ^ (e - 1))*y)+f.sum fun e a => (a*(poly_binom_aux1 x y e a).val)*y ^ 2 :=
  by 
    rw [poly_binom_aux2]
    simp [left_distrib, sum_add, mul_assocₓ]

/--
A polynomial `f` evaluated at `x + y` can be expressed as
the evaluation of `f` at `x`, plus `y` times the (polynomial) derivative of `f` at `x`,
plus some element `k : R` times `y^2`.
-/
def binom_expansion (f : Polynomial R) (x y : R) :
  { k : R // f.eval (x+y) = (f.eval x+f.derivative.eval x*y)+k*y ^ 2 } :=
  by 
    exists f.sum fun e a => a*(poly_binom_aux1 x y e a).val 
    rw [poly_binom_aux3]
    congr
    ·
      rw [←eval_eq_sum]
    ·
      rw [derivative_eval]
      exact finset.sum_mul.symm
    ·
      exact finset.sum_mul.symm

/--
`x^n - y^n` can be expressed as `z * (x - y)` for some `z` in the ring.
-/
def pow_sub_pow_factor (x y : R) : ∀ i : ℕ, { z : R // x ^ i - y ^ i = z*x - y }
| 0 =>
  ⟨0,
    by 
      simp ⟩
| 1 =>
  ⟨1,
    by 
      simp ⟩
| k+2 =>
  by 
    cases' @pow_sub_pow_factor (k+1) with z hz 
    exists (z*x)+y ^ k+1
    calc ((x ^ k+2) - y ^ k+2) = (x*(x ^ k+1) - y ^ k+1)+(x*y ^ k+1) - y ^ k+2 :=
      by 
        ringExp _ = (x*z*x - y)+(x*y ^ k+1) - y ^ k+2 :=
      by 
        rw [hz]_ = ((z*x)+y ^ k+1)*x - y :=
      by 
        ringExp

/--
For any polynomial `f`, `f.eval x - f.eval y` can be expressed as `z * (x - y)`
for some `z` in the ring.
-/
def eval_sub_factor (f : Polynomial R) (x y : R) : { z : R // f.eval x - f.eval y = z*x - y } :=
  by 
    refine' ⟨f.sum fun i r => r*(pow_sub_pow_factor x y i).val, _⟩
    delta' eval eval₂ 
    simp only [Sum, ←Finset.sum_sub_distrib, Finset.sum_mul]
    dsimp 
    congr with i r 
    rw [mul_assocₓ, ←(pow_sub_pow_factor x y _).Prop, mul_sub]

end Identities

end Polynomial

