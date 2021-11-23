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

-- error in Data.Polynomial.HasseDeriv: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem factorial_smul_hasse_deriv : «expr = »(«expr⇑ »(«expr • »(«expr !»(k), @hasse_deriv R _ k)), «expr ^[ ]»(@derivative R _, k)) :=
begin
  induction [expr k] [] ["with", ident k, ident ih] [],
  { rw ["[", expr hasse_deriv_zero, ",", expr factorial_zero, ",", expr iterate_zero, ",", expr one_smul, ",", expr linear_map.id_coe, "]"] [] },
  ext [] [ident f, ident n] [":", 2],
  rw ["[", expr iterate_succ_apply', ",", "<-", expr ih, "]"] [],
  simp [] [] ["only"] ["[", expr linear_map.smul_apply, ",", expr coeff_smul, ",", expr linear_map.map_smul_of_tower, ",", expr coeff_derivative, ",", expr hasse_deriv_coeff, ",", "<-", expr @choose_symm_add _ k, "]"] [] [],
  simp [] [] ["only"] ["[", expr nsmul_eq_mul, ",", expr factorial_succ, ",", expr mul_assoc, ",", expr succ_eq_add_one, ",", "<-", expr add_assoc, ",", expr add_right_comm n 1 k, ",", "<-", expr cast_succ, "]"] [] [],
  rw ["<-", expr (cast_commute «expr + »(n, 1) (f.coeff «expr + »(«expr + »(n, k), 1))).eq] [],
  simp [] [] ["only"] ["[", "<-", expr mul_assoc, "]"] [] [],
  norm_cast [],
  congr' [2] [],
  apply [expr @cast_injective exprℚ()],
  have [ident h1] [":", expr «expr ≤ »(«expr + »(n, 1), «expr + »(«expr + »(n, k), 1))] [":=", expr succ_le_succ le_self_add],
  have [ident h2] [":", expr «expr ≤ »(«expr + »(k, 1), «expr + »(«expr + »(n, k), 1))] [":=", expr succ_le_succ le_add_self],
  have [ident H] [":", expr ∀ n : exprℕ(), «expr ≠ »((«expr !»(n) : exprℚ()), 0)] [],
  { exact_mod_cast [expr factorial_ne_zero] },
  simp [] [] ["only"] ["[", expr cast_mul, ",", expr cast_choose exprℚ(), ",", expr h1, ",", expr h2, ",", "-", ident one_div, ",", "-", ident mul_eq_zero, ",", expr succ_sub_succ_eq_sub, ",", expr add_tsub_cancel_right, ",", expr add_tsub_cancel_left, "]"] ["with", ident field_simps] [],
  rw ["[", expr eq_div_iff_mul_eq (mul_ne_zero (H _) (H _)), ",", expr eq_comm, ",", expr div_mul_eq_mul_div, ",", expr eq_div_iff_mul_eq (mul_ne_zero (H _) (H _)), "]"] [],
  norm_cast [],
  simp [] [] ["only"] ["[", expr factorial_succ, ",", expr succ_eq_add_one, "]"] [] [],
  ring []
end

-- error in Data.Polynomial.HasseDeriv: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem hasse_deriv_comp
(k
 l : exprℕ()) : «expr = »((@hasse_deriv R _ k).comp (hasse_deriv l), «expr • »(«expr + »(k, l).choose k, hasse_deriv «expr + »(k, l))) :=
begin
  ext [] [ident i] [":", 2],
  simp [] [] ["only"] ["[", expr linear_map.smul_apply, ",", expr comp_app, ",", expr linear_map.coe_comp, ",", expr smul_monomial, ",", expr hasse_deriv_apply, ",", expr mul_one, ",", expr monomial_eq_zero_iff, ",", expr sum_monomial_index, ",", expr mul_zero, ",", "<-", expr tsub_add_eq_tsub_tsub, ",", expr add_comm l k, "]"] [] [],
  rw_mod_cast [expr nsmul_eq_mul] [],
  congr' [2] [],
  by_cases [expr hikl, ":", expr «expr < »(i, «expr + »(k, l))],
  { rw ["[", expr choose_eq_zero_of_lt hikl, ",", expr mul_zero, "]"] [],
    by_cases [expr hil, ":", expr «expr < »(i, l)],
    { rw ["[", expr choose_eq_zero_of_lt hil, ",", expr mul_zero, "]"] [] },
    { push_neg ["at", ident hil],
      rw ["[", "<-", expr tsub_lt_iff_right hil, "]"] ["at", ident hikl],
      rw ["[", expr choose_eq_zero_of_lt hikl, ",", expr zero_mul, "]"] [] } },
  push_neg ["at", ident hikl],
  apply [expr @cast_injective exprℚ()],
  have [ident h1] [":", expr «expr ≤ »(l, i)] [":=", expr nat.le_of_add_le_right hikl],
  have [ident h2] [":", expr «expr ≤ »(k, «expr - »(i, l))] [":=", expr le_tsub_of_add_le_right hikl],
  have [ident h3] [":", expr «expr ≤ »(k, «expr + »(k, l))] [":=", expr le_self_add],
  have [ident H] [":", expr ∀ n : exprℕ(), «expr ≠ »((«expr !»(n) : exprℚ()), 0)] [],
  { exact_mod_cast [expr factorial_ne_zero] },
  simp [] [] ["only"] ["[", expr cast_mul, ",", expr cast_choose exprℚ(), ",", expr h1, ",", expr h2, ",", expr h3, ",", expr hikl, ",", "-", ident one_div, ",", "-", ident mul_eq_zero, ",", expr succ_sub_succ_eq_sub, ",", expr add_tsub_cancel_right, ",", expr add_tsub_cancel_left, "]"] ["with", ident field_simps] [],
  rw ["[", expr eq_div_iff_mul_eq, ",", expr eq_comm, ",", expr div_mul_eq_mul_div, ",", expr eq_div_iff_mul_eq, ",", "<-", expr tsub_add_eq_tsub_tsub, ",", expr add_comm l k, "]"] [],
  { ring [] },
  all_goals { apply_rules ["[", expr mul_ne_zero, ",", expr H, "]"] }
end

section 

open AddMonoidHom Finset.Nat

-- error in Data.Polynomial.HasseDeriv: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem hasse_deriv_mul
(f
 g : polynomial R) : «expr = »(hasse_deriv k «expr * »(f, g), «expr∑ in , »((ij), antidiagonal k, «expr * »(hasse_deriv ij.1 f, hasse_deriv ij.2 g))) :=
begin
  let [ident D] [] [":=", expr λ k, (@hasse_deriv R _ k).to_add_monoid_hom],
  let [ident Φ] [] [":=", expr @add_monoid_hom.mul (polynomial R) _],
  show [expr «expr = »((comp_hom (D k)).comp Φ f g, «expr∑ in , »((ij : «expr × »(exprℕ(), exprℕ())), antidiagonal k, (comp_hom.comp (comp_hom Φ (D ij.1))).flip (D ij.2) f g))],
  simp [] [] ["only"] ["[", "<-", expr finset_sum_apply, "]"] [] [],
  congr' [2] [],
  clear [ident f, ident g],
  ext [] [ident m, ident r, ident n, ident s] [":", 4],
  simp [] [] ["only"] ["[", expr finset_sum_apply, ",", expr coe_mul_left, ",", expr coe_comp, ",", expr flip_apply, ",", expr comp_app, ",", expr hasse_deriv_monomial, ",", expr linear_map.to_add_monoid_hom_coe, ",", expr comp_hom_apply_apply, ",", expr coe_mul, ",", expr monomial_mul_monomial, "]"] [] [],
  have [ident aux] [":", expr ∀
   x : «expr × »(exprℕ(), exprℕ()), «expr ∈ »(x, antidiagonal k) → «expr = »(monomial «expr + »(«expr - »(m, x.1), «expr - »(n, x.2)) «expr * »(«expr * »(«expr↑ »(m.choose x.1), r), «expr * »(«expr↑ »(n.choose x.2), s)), monomial «expr - »(«expr + »(m, n), k) «expr * »(«expr * »(«expr↑ »(m.choose x.1), «expr↑ »(n.choose x.2)), «expr * »(r, s)))] [],
  { intros [ident x, ident hx],
    rw ["[", expr finset.nat.mem_antidiagonal, "]"] ["at", ident hx],
    subst [expr hx],
    by_cases [expr hm, ":", expr «expr < »(m, x.1)],
    { simp [] [] ["only"] ["[", expr nat.choose_eq_zero_of_lt hm, ",", expr nat.cast_zero, ",", expr zero_mul, ",", expr monomial_zero_right, "]"] [] [] },
    by_cases [expr hn, ":", expr «expr < »(n, x.2)],
    { simp [] [] ["only"] ["[", expr nat.choose_eq_zero_of_lt hn, ",", expr nat.cast_zero, ",", expr zero_mul, ",", expr mul_zero, ",", expr monomial_zero_right, "]"] [] [] },
    push_neg ["at", ident hm, ident hn],
    rw ["[", expr tsub_add_eq_add_tsub hm, ",", "<-", expr add_tsub_assoc_of_le hn, ",", "<-", expr tsub_add_eq_tsub_tsub, ",", expr add_comm x.2 x.1, ",", expr mul_assoc, ",", "<-", expr mul_assoc r, ",", "<-", expr (nat.cast_commute _ r).eq, ",", expr mul_assoc, ",", expr mul_assoc, "]"] [] },
  conv_rhs [] [] { apply_congr [],
    skip,
    rw [expr aux _ H] },
  rw_mod_cast ["[", "<-", expr linear_map.map_sum, ",", "<-", expr finset.sum_mul, ",", "<-", expr nat.add_choose_eq, "]"] []
end

end 

end Polynomial

