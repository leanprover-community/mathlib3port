import Mathbin.Data.Nat.Choose.Cast 
import Mathbin.Data.Nat.Choose.Vandermonde 
import Mathbin.Data.Polynomial.Derivative

/-!
# Hasse derivative of polynomials

The `k`th Hasse derivative of a polynomial `∑ a_i X^i` is `∑ (i.choose k) a_i X^(i-k)`.
It is a variant of the usual derivative, and satisfies `k! * (hasse_deriv k f) = derivative^[k] f`.
The main benefit is that is gives an atomic way of talking about expressions such as
`(derivative^[k] f).eval r / k!`, that occur in Taylor expansions, for example.

## Main declarations

In the following, we write `D k` for the `k`-th Hasse derivative `hasse_deriv k`.

* `polynomial.hasse_deriv`: the `k`-th Hasse derivative of a polynomial
* `polynomial.hasse_deriv_zero`: the `0`th Hasse derivative is the identity
* `polynomial.hasse_deriv_one`: the `1`st Hasse derivative is the usual derivative
* `polynomial.factorial_smul_hasse_deriv`: the identity `k! • (D k f) = derivative^[k] f`
* `polynomial.hasse_deriv_comp`: the identity `(D k).comp (D l) = (k+l).choose k • D (k+l)`
* `polynomial.hasse_deriv_mul`:
  the "Leibniz rule" `D k (f * g) = ∑ ij in antidiagonal k, D ij.1 f * D ij.2 g`

For the identity principle, see `polynomial.eq_zero_of_hasse_deriv_eq_zero`
in `data/polynomial/taylor.lean`.

## Reference

https://math.fontein.de/2009/08/12/the-hasse-derivative/

-/


noncomputable theory

namespace Polynomial

open_locale Nat BigOperators

open Function

open Nat hiding nsmul_eq_mul

variable{R : Type _}[Semiringₓ R](k : ℕ)(f : Polynomial R)

/-- The `k`th Hasse derivative of a polynomial `∑ a_i X^i` is `∑ (i.choose k) a_i X^(i-k)`.
It satisfies `k! * (hasse_deriv k f) = derivative^[k] f`. -/
def hasse_deriv (k : ℕ) : Polynomial R →ₗ[R] Polynomial R :=
  lsum fun i => monomial (i - k) ∘ₗ DistribMulAction.toLinearMap R R (i.choose k)

theorem hasse_deriv_apply : hasse_deriv k f = f.sum fun i r => monomial (i - k) («expr↑ » (i.choose k)*r) :=
  by 
    simpa only [←nsmul_eq_mul]

theorem hasse_deriv_coeff (n : ℕ) : (hasse_deriv k f).coeff n = (n+k).choose k*f.coeff (n+k) :=
  by 
    rw [hasse_deriv_apply, coeff_sum, sum_def, Finset.sum_eq_single (n+k), coeff_monomial]
    ·
      simp only [if_true, add_tsub_cancel_right, eq_self_iff_true]
    ·
      intro i hi hink 
      rw [coeff_monomial]
      byCases' hik : i < k
      ·
        simp only [Nat.choose_eq_zero_of_lt hik, if_t_t, Nat.cast_zero, zero_mul]
      ·
        pushNeg  at hik 
        rw [if_neg]
        contrapose! hink 
        exact (tsub_eq_iff_eq_add_of_le hik).mp hink
    ·
      intro h 
      simp only [not_mem_support_iff.mp h, monomial_zero_right, mul_zero, coeff_zero]

theorem hasse_deriv_zero' : hasse_deriv 0 f = f :=
  by 
    simp only [hasse_deriv_apply, tsub_zero, Nat.choose_zero_right, Nat.cast_one, one_mulₓ, sum_monomial_eq]

@[simp]
theorem hasse_deriv_zero : @hasse_deriv R _ 0 = LinearMap.id :=
  LinearMap.ext$ hasse_deriv_zero'

theorem hasse_deriv_one' : hasse_deriv 1 f = derivative f :=
  by 
    simp only [hasse_deriv_apply, derivative_apply, monomial_eq_C_mul_X, Nat.choose_one_right,
      (Nat.cast_commute _ _).Eq]

@[simp]
theorem hasse_deriv_one : @hasse_deriv R _ 1 = derivative :=
  LinearMap.ext$ hasse_deriv_one'

@[simp]
theorem hasse_deriv_monomial (n : ℕ) (r : R) :
  hasse_deriv k (monomial n r) = monomial (n - k) («expr↑ » (n.choose k)*r) :=
  by 
    ext i 
    simp only [hasse_deriv_coeff, coeff_monomial]
    byCases' hnik : n = i+k
    ·
      rw [if_pos hnik, if_pos, ←hnik]
      apply tsub_eq_of_eq_add_rev 
      rwa [add_commₓ]
    ·
      rw [if_neg hnik, mul_zero]
      byCases' hkn : k ≤ n
      ·
        rw [←tsub_eq_iff_eq_add_of_le hkn] at hnik 
        rw [if_neg hnik]
      ·
        pushNeg  at hkn 
        rw [Nat.choose_eq_zero_of_lt hkn, Nat.cast_zero, zero_mul, if_t_t]

theorem hasse_deriv_C (r : R) (hk : 0 < k) : hasse_deriv k (C r) = 0 :=
  by 
    rw [←monomial_zero_left, hasse_deriv_monomial, Nat.choose_eq_zero_of_lt hk, Nat.cast_zero, zero_mul,
      monomial_zero_right]

theorem hasse_deriv_apply_one (hk : 0 < k) : hasse_deriv k (1 : Polynomial R) = 0 :=
  by 
    rw [←C_1, hasse_deriv_C k _ hk]

theorem hasse_deriv_X (hk : 1 < k) : hasse_deriv k (X : Polynomial R) = 0 :=
  by 
    rw [←monomial_one_one_eq_X, hasse_deriv_monomial, Nat.choose_eq_zero_of_lt hk, Nat.cast_zero, zero_mul,
      monomial_zero_right]

theorem factorial_smul_hasse_deriv : «expr⇑ » (k ! • @hasse_deriv R _ k) = @derivative R _^[k] :=
  by 
    induction' k with k ih
    ·
      rw [hasse_deriv_zero, factorial_zero, iterate_zero, one_smul, LinearMap.id_coe]
    ext f n : 2
    rw [iterate_succ_apply', ←ih]
    simp only [LinearMap.smul_apply, coeff_smul, LinearMap.map_smul_of_tower, coeff_derivative, hasse_deriv_coeff,
      ←@choose_symm_add _ k]
    simp only [nsmul_eq_mul, factorial_succ, mul_assocₓ, succ_eq_add_one, ←add_assocₓ, add_right_commₓ n 1 k,
      ←cast_succ]
    rw [←(cast_commute (n+1) (f.coeff ((n+k)+1))).Eq]
    simp only [←mul_assocₓ]
    normCast 
    congr 2
    apply @cast_injective ℚ 
    have h1 : (n+1) ≤ (n+k)+1 := succ_le_succ le_self_add 
    have h2 : (k+1) ≤ (n+k)+1 := succ_le_succ le_add_self 
    have H : ∀ n : ℕ, (n ! : ℚ) ≠ 0
    ·
      exactModCast factorial_ne_zero 
    simp' only [cast_mul, cast_choose ℚ, h1, h2, -one_div, -mul_eq_zero, succ_sub_succ_eq_sub, add_tsub_cancel_right,
      add_tsub_cancel_left] with field_simps 
    rw [eq_div_iff_mul_eq (mul_ne_zero (H _) (H _)), eq_comm, div_mul_eq_mul_div,
      eq_div_iff_mul_eq (mul_ne_zero (H _) (H _))]
    normCast 
    simp only [factorial_succ, succ_eq_add_one]
    ring

theorem hasse_deriv_comp (k l : ℕ) : (@hasse_deriv R _ k).comp (hasse_deriv l) = (k+l).choose k • hasse_deriv (k+l) :=
  by 
    ext i : 2
    simp only [LinearMap.smul_apply, comp_app, LinearMap.coe_comp, smul_monomial, hasse_deriv_apply, mul_oneₓ,
      monomial_eq_zero_iff, sum_monomial_index, mul_zero, ←tsub_add_eq_tsub_tsub, add_commₓ l k]
    rwModCast [nsmul_eq_mul]
    congr 2
    byCases' hikl : i < k+l
    ·
      rw [choose_eq_zero_of_lt hikl, mul_zero]
      byCases' hil : i < l
      ·
        rw [choose_eq_zero_of_lt hil, mul_zero]
      ·
        pushNeg  at hil 
        rw [←tsub_lt_iff_right hil] at hikl 
        rw [choose_eq_zero_of_lt hikl, zero_mul]
    pushNeg  at hikl 
    apply @cast_injective ℚ 
    have h1 : l ≤ i := Nat.le_of_add_le_right hikl 
    have h2 : k ≤ i - l := le_tsub_of_add_le_right hikl 
    have h3 : k ≤ k+l := le_self_add 
    have H : ∀ n : ℕ, (n ! : ℚ) ≠ 0
    ·
      exactModCast factorial_ne_zero 
    simp' only [cast_mul, cast_choose ℚ, h1, h2, h3, hikl, -one_div, -mul_eq_zero, succ_sub_succ_eq_sub,
      add_tsub_cancel_right, add_tsub_cancel_left] with field_simps 
    rw [eq_div_iff_mul_eq, eq_comm, div_mul_eq_mul_div, eq_div_iff_mul_eq, ←tsub_add_eq_tsub_tsub, add_commₓ l k]
    ·
      ring 
    all_goals 
      applyRules [mul_ne_zero, H]

section 

open AddMonoidHom Finset.Nat

theorem hasse_deriv_mul (f g : Polynomial R) :
  hasse_deriv k (f*g) = ∑ij in antidiagonal k, hasse_deriv ij.1 f*hasse_deriv ij.2 g :=
  by 
    let D := fun k => (@hasse_deriv R _ k).toAddMonoidHom 
    let Φ := @AddMonoidHom.mul (Polynomial R) _ 
    show
      (comp_hom (D k)).comp Φ f g =
        ∑ij : ℕ × ℕ in antidiagonal k, ((comp_hom.comp ((comp_hom Φ) (D ij.1))).flip (D ij.2) f) g 
    simp only [←finset_sum_apply]
    congr 2
    clear f g 
    ext m r n s : 4
    simp only [finset_sum_apply, coe_mul_left, coe_comp, flip_apply, comp_app, hasse_deriv_monomial,
      LinearMap.to_add_monoid_hom_coe, comp_hom_apply_apply, coe_mul, monomial_mul_monomial]
    have aux :
      ∀ x : ℕ × ℕ,
        x ∈ antidiagonal k →
          monomial ((m - x.1)+n - x.2) ((«expr↑ » (m.choose x.1)*r)*«expr↑ » (n.choose x.2)*s) =
            monomial ((m+n) - k) ((«expr↑ » (m.choose x.1)*«expr↑ » (n.choose x.2))*r*s)
    ·
      intro x hx 
      rw [Finset.Nat.mem_antidiagonal] at hx 
      subst hx 
      byCases' hm : m < x.1
      ·
        simp only [Nat.choose_eq_zero_of_lt hm, Nat.cast_zero, zero_mul, monomial_zero_right]
      byCases' hn : n < x.2
      ·
        simp only [Nat.choose_eq_zero_of_lt hn, Nat.cast_zero, zero_mul, mul_zero, monomial_zero_right]
      pushNeg  at hm hn 
      rw [tsub_add_eq_add_tsub hm, ←add_tsub_assoc_of_le hn, ←tsub_add_eq_tsub_tsub, add_commₓ x.2 x.1, mul_assocₓ,
        ←mul_assocₓ r, ←(Nat.cast_commute _ r).Eq, mul_assocₓ, mul_assocₓ]
    convRHS => applyCongr skip rw [aux _ H]
    rwModCast [←LinearMap.map_sum, ←Finset.sum_mul, ←Nat.add_choose_eq]

end 

end Polynomial

