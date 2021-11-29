import Mathbin.Data.Polynomial.RingDivision

/-!
# "Mirror" of a univariate polynomial

In this file we define `polynomial.mirror`, a variant of `polynomial.reverse`. The difference
between `reverse` and `mirror` is that `reverse` will decrease the degree if the polynomial is
divisible by `X`. We also define `polynomial.norm2`, which is the sum of the squares of the
coefficients of a polynomial. It is also a coefficient of `p * p.mirror`.

## Main definitions

- `polynomial.mirror`
- `polynomial.norm2`

## Main results

- `polynomial.mirror_mul_of_domain`: `mirror` preserves multiplication.
- `polynomial.irreducible_of_mirror`: an irreducibility criterion involving `mirror`
- `polynomial.norm2_eq_mul_reverse_coeff`: `norm2` is a coefficient of `p * p.mirror`

-/


namespace Polynomial

variable {R : Type _} [Semiringₓ R] (p : Polynomial R)

section Mirror

/-- mirror of a polynomial: reverses the coefficients while preserving `polynomial.nat_degree` -/
noncomputable def mirror :=
  p.reverse*X ^ p.nat_trailing_degree

@[simp]
theorem mirror_zero : (0 : Polynomial R).mirror = 0 :=
  by 
    simp [mirror]

theorem mirror_monomial (n : ℕ) (a : R) : (monomial n a).mirror = monomial n a :=
  by 
    byCases' ha : a = 0
    ·
      rw [ha, monomial_zero_right, mirror_zero]
    ·
      rw [mirror, reverse, nat_degree_monomial n a ha, nat_trailing_degree_monomial ha, ←C_mul_X_pow_eq_monomial,
        reflect_C_mul_X_pow, rev_at_le (le_reflₓ n), tsub_self, pow_zeroₓ, mul_oneₓ]

theorem mirror_C (a : R) : (C a).mirror = C a :=
  mirror_monomial 0 a

theorem mirror_X : X.mirror = (X : Polynomial R) :=
  mirror_monomial 1 (1 : R)

-- error in Data.Polynomial.Mirror: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem mirror_nat_degree : «expr = »(p.mirror.nat_degree, p.nat_degree) :=
begin
  by_cases [expr hp, ":", expr «expr = »(p, 0)],
  { rw ["[", expr hp, ",", expr mirror_zero, "]"] [] },
  by_cases [expr hR, ":", expr nontrivial R],
  { haveI [] [] [":=", expr hR],
    rw ["[", expr mirror, ",", expr nat_degree_mul', ",", expr reverse_nat_degree, ",", expr nat_degree_X_pow, ",", expr tsub_add_cancel_of_le p.nat_trailing_degree_le_nat_degree, "]"] [],
    rwa ["[", expr leading_coeff_X_pow, ",", expr mul_one, ",", expr reverse_leading_coeff, ",", expr ne, ",", expr trailing_coeff_eq_zero, "]"] [] },
  { haveI [] [] [":=", expr not_nontrivial_iff_subsingleton.mp hR],
    exact [expr congr_arg nat_degree (subsingleton.elim p.mirror p)] }
end

theorem mirror_nat_trailing_degree : p.mirror.nat_trailing_degree = p.nat_trailing_degree :=
  by 
    byCases' hp : p = 0
    ·
      rw [hp, mirror_zero]
    ·
      rw [mirror, nat_trailing_degree_mul_X_pow ((mt reverse_eq_zero.mp) hp), reverse_nat_trailing_degree, zero_addₓ]

theorem coeff_mirror (n : ℕ) : p.mirror.coeff n = p.coeff (rev_at (p.nat_degree+p.nat_trailing_degree) n) :=
  by 
    byCases' h2 : p.nat_degree < n
    ·
      rw
        [coeff_eq_zero_of_nat_degree_lt
          (by 
            rwa [mirror_nat_degree])]
      byCases' h1 : n ≤ p.nat_degree+p.nat_trailing_degree
      ·
        rw [rev_at_le h1, coeff_eq_zero_of_lt_nat_trailing_degree]
        exact (tsub_lt_iff_left h1).mpr (Nat.add_lt_add_rightₓ h2 _)
      ·
        rw [←rev_at_fun_eq, rev_at_fun, if_neg h1, coeff_eq_zero_of_nat_degree_lt h2]
    rw [not_ltₓ] at h2 
    rw [rev_at_le (h2.trans (Nat.le_add_rightₓ _ _))]
    byCases' h3 : p.nat_trailing_degree ≤ n
    ·
      rw [←tsub_add_eq_add_tsub h2, ←tsub_tsub_assoc h2 h3, mirror, coeff_mul_X_pow', if_pos h3, coeff_reverse,
        rev_at_le (tsub_le_self.trans h2)]
    rw [not_leₓ] at h3 
    rw [coeff_eq_zero_of_nat_degree_lt (lt_tsub_iff_right.mpr (Nat.add_lt_add_leftₓ h3 _))]
    exact
      coeff_eq_zero_of_lt_nat_trailing_degree
        (by 
          rwa [mirror_nat_trailing_degree])

theorem mirror_eval_one : p.mirror.eval 1 = p.eval 1 :=
  by 
    simpRw [eval_eq_finset_sum, one_pow, mul_oneₓ, mirror_nat_degree]
    refine' Finset.sum_bij_ne_zero _ _ _ _ _
    ·
      exact fun n hn hp => rev_at (p.nat_degree+p.nat_trailing_degree) n
    ·
      intro n hn hp 
      rw [Finset.mem_range_succ_iff] at *
      rw [rev_at_le (hn.trans (Nat.le_add_rightₓ _ _))]
      rw [tsub_le_iff_tsub_le, add_commₓ, add_tsub_cancel_right, ←mirror_nat_trailing_degree]
      exact nat_trailing_degree_le_of_ne_zero hp
    ·
      exact
        fun n₁ n₂ hn₁ hp₁ hn₂ hp₂ h =>
          by 
            rw [←@rev_at_invol _ n₁, h, rev_at_invol]
    ·
      intro n hn hp 
      use rev_at (p.nat_degree+p.nat_trailing_degree) n 
      refine' ⟨_, _, rev_at_invol.symm⟩
      ·
        rw [Finset.mem_range_succ_iff] at *
        rw [rev_at_le (hn.trans (Nat.le_add_rightₓ _ _))]
        rw [tsub_le_iff_tsub_le, add_commₓ, add_tsub_cancel_right]
        exact nat_trailing_degree_le_of_ne_zero hp
      ·
        change p.mirror.coeff _ ≠ 0
        rwa [coeff_mirror, rev_at_invol]
    ·
      exact fun n hn hp => p.coeff_mirror n

theorem mirror_mirror : p.mirror.mirror = p :=
  Polynomial.ext
    fun n =>
      by 
        rw [coeff_mirror, coeff_mirror, mirror_nat_degree, mirror_nat_trailing_degree, rev_at_invol]

theorem mirror_eq_zero : p.mirror = 0 ↔ p = 0 :=
  ⟨fun h =>
      by 
        rw [←p.mirror_mirror, h, mirror_zero],
    fun h =>
      by 
        rw [h, mirror_zero]⟩

theorem mirror_trailing_coeff : p.mirror.trailing_coeff = p.leading_coeff :=
  by 
    rw [leading_coeff, trailing_coeff, mirror_nat_trailing_degree, coeff_mirror, rev_at_le (Nat.le_add_leftₓ _ _),
      add_tsub_cancel_right]

theorem mirror_leading_coeff : p.mirror.leading_coeff = p.trailing_coeff :=
  by 
    rw [←p.mirror_mirror, mirror_trailing_coeff, p.mirror_mirror]

theorem mirror_mul_of_domain {R : Type _} [Ringₓ R] [IsDomain R] (p q : Polynomial R) :
  (p*q).mirror = p.mirror*q.mirror :=
  by 
    byCases' hp : p = 0
    ·
      rw [hp, zero_mul, mirror_zero, zero_mul]
    byCases' hq : q = 0
    ·
      rw [hq, mul_zero, mirror_zero, mul_zero]
    rw [mirror, mirror, mirror, reverse_mul_of_domain, nat_trailing_degree_mul hp hq, pow_addₓ]
    rw [mul_assocₓ, ←mul_assocₓ q.reverse]
    convLHS => congr skip congr rw [←X_pow_mul]
    repeat' 
      rw [mul_assocₓ]

theorem mirror_smul {R : Type _} [Ringₓ R] [IsDomain R] (p : Polynomial R) (a : R) : (a • p).mirror = a • p.mirror :=
  by 
    rw [←C_mul', ←C_mul', mirror_mul_of_domain, mirror_C]

theorem mirror_neg {R : Type _} [Ringₓ R] (p : Polynomial R) : (-p).mirror = -p.mirror :=
  by 
    rw [mirror, mirror, reverse_neg, nat_trailing_degree_neg, neg_mul_eq_neg_mul]

-- error in Data.Polynomial.Mirror: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem irreducible_of_mirror
{R : Type*}
[comm_ring R]
[is_domain R]
{f : polynomial R}
(h1 : «expr¬ »(is_unit f))
(h2 : ∀
 k, «expr = »(«expr * »(f, f.mirror), «expr * »(k, k.mirror)) → «expr ∨ »(«expr = »(k, f), «expr ∨ »(«expr = »(k, «expr- »(f)), «expr ∨ »(«expr = »(k, f.mirror), «expr = »(k, «expr- »(f.mirror))))))
(h3 : ∀ g, «expr ∣ »(g, f) → «expr ∣ »(g, f.mirror) → is_unit g) : irreducible f :=
begin
  split,
  { exact [expr h1] },
  { intros [ident g, ident h, ident fgh],
    let [ident k] [] [":=", expr «expr * »(g, h.mirror)],
    have [ident key] [":", expr «expr = »(«expr * »(f, f.mirror), «expr * »(k, k.mirror))] [],
    { rw ["[", expr fgh, ",", expr mirror_mul_of_domain, ",", expr mirror_mul_of_domain, ",", expr mirror_mirror, ",", expr mul_assoc, ",", expr mul_comm h, ",", expr mul_comm g.mirror, ",", expr mul_assoc, ",", "<-", expr mul_assoc, "]"] [] },
    have [ident g_dvd_f] [":", expr «expr ∣ »(g, f)] [],
    { rw [expr fgh] [],
      exact [expr dvd_mul_right g h] },
    have [ident h_dvd_f] [":", expr «expr ∣ »(h, f)] [],
    { rw [expr fgh] [],
      exact [expr dvd_mul_left h g] },
    have [ident g_dvd_k] [":", expr «expr ∣ »(g, k)] [],
    { exact [expr dvd_mul_right g h.mirror] },
    have [ident h_dvd_k_rev] [":", expr «expr ∣ »(h, k.mirror)] [],
    { rw ["[", expr mirror_mul_of_domain, ",", expr mirror_mirror, "]"] [],
      exact [expr dvd_mul_left h g.mirror] },
    have [ident hk] [] [":=", expr h2 k key],
    rcases [expr hk, "with", ident hk, "|", ident hk, "|", ident hk, "|", ident hk],
    { exact [expr or.inr (h3 h h_dvd_f (by rwa ["<-", expr hk] []))] },
    { exact [expr or.inr (h3 h h_dvd_f (by rwa ["[", expr eq_neg_iff_eq_neg.mp hk, ",", expr mirror_neg, ",", expr dvd_neg, "]"] []))] },
    { exact [expr or.inl (h3 g g_dvd_f (by rwa ["<-", expr hk] []))] },
    { exact [expr or.inl (h3 g g_dvd_f (by rwa ["[", expr eq_neg_iff_eq_neg.mp hk, ",", expr dvd_neg, "]"] []))] } }
end

end Mirror

end Polynomial

