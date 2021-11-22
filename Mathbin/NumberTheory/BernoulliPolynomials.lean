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

- `sum_bernoulli_poly`: The sum of the $k^\mathrm{th}$ Bernoulli polynomial with binomial
  coefficients up to n is `(n + 1) * X^n`.
- `exp_bernoulli_poly`: The Bernoulli polynomials act as generating functions for the exponential.

## TODO

- `bernoulli_poly_eval_one_neg` : $$ B_n(1 - x) = (-1)^n*B_n(x) $$
- ``bernoulli_poly_eval_one` : Follows as a consequence of `bernoulli_poly_eval_one_neg`.

-/


noncomputable theory

open_locale BigOperators

open_locale Nat

open Nat Finset

/-- The Bernoulli polynomials are defined in terms of the negative Bernoulli numbers. -/
def bernoulliPoly (n : ℕ) : Polynomial ℚ :=
  ∑i in range (n+1), Polynomial.monomial (n - i) (bernoulli i*choose n i)

theorem bernoulli_poly_def (n : ℕ) :
  bernoulliPoly n = ∑i in range (n+1), Polynomial.monomial i (bernoulli (n - i)*choose n i) :=
  by 
    rw [←sum_range_reflect, add_succ_sub_one, add_zeroₓ, bernoulliPoly]
    apply sum_congr rfl 
    rintro x hx 
    rw [mem_range_succ_iff] at hx 
    rw [choose_symm hx, tsub_tsub_cancel_of_le hx]

namespace bernoulliPoly

section Examples

@[simp]
theorem bernoulli_poly_zero : bernoulliPoly 0 = 1 :=
  by 
    simp [bernoulliPoly]

@[simp]
theorem bernoulli_poly_eval_zero (n : ℕ) : (bernoulliPoly n).eval 0 = bernoulli n :=
  by 
    rw [bernoulliPoly, Polynomial.eval_finset_sum, sum_range_succ]
    have  : (∑x : ℕ in range n, (bernoulli x*n.choose x)*0^n - x) = 0
    ·
      apply sum_eq_zero fun x hx => _ 
      have h : 0 < n - x := tsub_pos_of_lt (mem_range.1 hx)
      simp [h]
    simp [this]

@[simp]
theorem bernoulli_poly_eval_one (n : ℕ) : (bernoulliPoly n).eval 1 = bernoulli' n :=
  by 
    simp only [bernoulliPoly, Polynomial.eval_finset_sum]
    simp only [←succ_eq_add_one, sum_range_succ, mul_oneₓ, cast_one, choose_self, (bernoulli _).mul_comm, sum_bernoulli,
      one_pow, mul_oneₓ, Polynomial.eval_C, Polynomial.eval_monomial]
    byCases' h : n = 1
    ·
      normNum [h]
    ·
      simp [h]
      exact bernoulli_eq_bernoulli'_of_ne_one h

end Examples

-- error in NumberTheory.BernoulliPolynomials: ././Mathport/Syntax/Translate/Basic.lean:340:40: in conv_lhs: ././Mathport/Syntax/Translate/Basic.lean:384:40: in conv: ././Mathport/Syntax/Translate/Tactic/Basic.lean:41:45: missing argument
@[simp]
theorem sum_bernoulli_poly
(n : exprℕ()) : «expr = »(«expr∑ in , »((k), range «expr + »(n, 1), «expr • »((«expr + »(n, 1).choose k : exprℚ()), bernoulli_poly k)), polynomial.monomial n («expr + »(n, 1) : exprℚ())) :=
begin
  simp_rw ["[", expr bernoulli_poly_def, ",", expr finset.smul_sum, ",", expr finset.range_eq_Ico, ",", "<-", expr finset.sum_Ico_Ico_comm, ",", expr finset.sum_Ico_eq_sum_range, "]"] [],
  simp [] [] ["only"] ["[", expr cast_succ, ",", expr add_tsub_cancel_left, ",", expr tsub_zero, ",", expr zero_add, ",", expr linear_map.map_add, "]"] [] [],
  simp_rw ["[", expr polynomial.smul_monomial, ",", expr mul_comm (bernoulli _) _, ",", expr smul_eq_mul, ",", "<-", expr mul_assoc, "]"] [],
  conv_lhs [] [] { apply_congr [],
    skip,
    conv { apply_congr [],
      skip,
      rw ["[", "<-", expr nat.cast_mul, ",", expr choose_mul «expr $ »(«expr $ »(le_tsub_iff_left, mem_range_le H).1, mem_range_le H_1) (le.intro rfl), ",", expr nat.cast_mul, ",", expr add_comm x x_1, ",", expr add_tsub_cancel_right, ",", expr mul_assoc, ",", expr mul_comm, ",", "<-", expr smul_eq_mul, ",", "<-", expr polynomial.smul_monomial, "]"] },
    rw ["[", "<-", expr sum_smul, "]"] },
  rw ["[", expr sum_range_succ_comm, "]"] [],
  simp [] [] ["only"] ["[", expr add_right_eq_self, ",", expr cast_succ, ",", expr mul_one, ",", expr cast_one, ",", expr cast_add, ",", expr add_tsub_cancel_left, ",", expr choose_succ_self_right, ",", expr one_smul, ",", expr bernoulli_zero, ",", expr sum_singleton, ",", expr zero_add, ",", expr linear_map.map_add, ",", expr range_one, "]"] [] [],
  apply [expr sum_eq_zero (λ x hx, _)],
  have [ident f] [":", expr ∀ x «expr ∈ » range n, «expr¬ »(«expr = »(«expr - »(«expr + »(n, 1), x), 1))] [],
  { rintros [ident x, ident H],
    rw ["[", expr mem_range, "]"] ["at", ident H],
    rw ["[", expr eq_comm, "]"] [],
    exact [expr ne_of_lt (nat.lt_of_lt_of_le one_lt_two (le_tsub_of_add_le_left (succ_le_succ H)))] },
  rw ["[", expr sum_bernoulli, "]"] [],
  have [ident g] [":", expr «expr = »(ite «expr = »(«expr - »(«expr + »(n, 1), x), 1) (1 : exprℚ()) 0, 0)] [],
  { simp [] [] ["only"] ["[", expr ite_eq_right_iff, ",", expr one_ne_zero, "]"] [] [],
    intro [ident h₁],
    exact [expr f x hx h₁] },
  rw ["[", expr g, ",", expr zero_smul, "]"] []
end

open PowerSeries

open polynomial(aeval)

variable{A : Type _}[CommRingₓ A][Algebra ℚ A]

/-- The theorem that `∑ Bₙ(t)X^n/n!)(e^X-1)=Xe^{tX}`  -/
theorem exp_bernoulli_poly' (t : A) :
  ((mk fun n => aeval t ((1 / n ! : ℚ) • bernoulliPoly n))*exp A - 1) = X*rescale t (exp A) :=
  by 
    ext n 
    cases n
    ·
      simp 
    rw [coeff_succ_X_mul, coeff_rescale, coeff_exp, coeff_mul, nat.sum_antidiagonal_eq_sum_range_succ_mk,
      sum_range_succ]
    simp only [RingHom.map_sub, tsub_self, constant_coeff_one, constant_coeff_exp, coeff_zero_eq_constant_coeff,
      mul_zero, sub_self, add_zeroₓ]
    set u : Units ℚ :=
      ⟨(n+1)!, (n+1)!⁻¹,
        mul_inv_cancel
          (by 
            exactModCast factorial_ne_zero (n+1)),
        inv_mul_cancel
          (by 
            exactModCast factorial_ne_zero (n+1))⟩ with
      hu 
    rw [←Units.mul_right_inj (Units.map (algebraMap ℚ A).toMonoidHom u)]
    rw [Units.coe_map, mul_left_commₓ, RingHom.to_monoid_hom_eq_coe, RingHom.coe_monoid_hom, ←RingHom.map_mul, hu,
      Units.coe_mk]
    change _ = (t^n)*algebraMap ℚ A (((n+1)*n ! : ℕ)*1 / n !)
    rw [cast_mul, mul_assocₓ, mul_one_div_cancel (show (n ! : ℚ) ≠ 0 from cast_ne_zero.2 (factorial_ne_zero n)),
      mul_oneₓ, mul_commₓ (t^n), ←Polynomial.aeval_monomial, cast_add, cast_one]
    rw [←sum_bernoulli_poly, Finset.mul_sum, AlgHom.map_sum]
    apply Finset.sum_congr rfl 
    intro i hi 
    simp only [Nat.cast_choose ℚ (mem_range_le hi), coeff_mk, if_neg (mem_range_sub_ne_zero hi), one_div,
      AlgHom.map_smul, coeff_one, Units.coe_mk, coeff_exp, sub_zero, LinearMap.map_sub, Algebra.smul_mul_assoc,
      Algebra.smul_def, mul_right_commₓ _ ((aeval t) _), ←mul_assocₓ, ←RingHom.map_mul, succ_eq_add_one]
    congr 
    apply congr_argₓ 
    rw [mul_assocₓ, div_eq_mul_inv, ←mul_inv₀]

end bernoulliPoly

