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

variable{R : Type _}[Semiringₓ R](p : Polynomial R)

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

theorem mirror_nat_degree : p.mirror.nat_degree = p.nat_degree :=
  by 
    byCases' hp : p = 0
    ·
      rw [hp, mirror_zero]
    byCases' hR : Nontrivial R
    ·
      haveI  := hR 
      rw [mirror, nat_degree_mul', reverse_nat_degree, nat_degree_X_pow,
        tsub_add_cancel_of_le p.nat_trailing_degree_le_nat_degree]
      rwa [leading_coeff_X_pow, mul_oneₓ, reverse_leading_coeff, Ne, trailing_coeff_eq_zero]
    ·
      haveI  := not_nontrivial_iff_subsingleton.mp hR 
      exact congr_argₓ nat_degree (Subsingleton.elimₓ p.mirror p)

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

-- error in Data.Polynomial.Mirror: ././Mathport/Syntax/Translate/Basic.lean:340:40: in repeat: ././Mathport/Syntax/Translate/Tactic/Basic.lean:41:45: missing argument
theorem mirror_mul_of_domain
{R : Type*}
[ring R]
[is_domain R]
(p q : polynomial R) : «expr = »(«expr * »(p, q).mirror, «expr * »(p.mirror, q.mirror)) :=
begin
  by_cases [expr hp, ":", expr «expr = »(p, 0)],
  { rw ["[", expr hp, ",", expr zero_mul, ",", expr mirror_zero, ",", expr zero_mul, "]"] [] },
  by_cases [expr hq, ":", expr «expr = »(q, 0)],
  { rw ["[", expr hq, ",", expr mul_zero, ",", expr mirror_zero, ",", expr mul_zero, "]"] [] },
  rw ["[", expr mirror, ",", expr mirror, ",", expr mirror, ",", expr reverse_mul_of_domain, ",", expr nat_trailing_degree_mul hp hq, ",", expr pow_add, "]"] [],
  rw ["[", expr mul_assoc, ",", "<-", expr mul_assoc q.reverse, "]"] [],
  conv_lhs [] [] { congr,
    skip,
    congr,
    rw ["[", "<-", expr X_pow_mul, "]"] },
  repeat { rw ["[", expr mul_assoc, "]"] [] }
end

theorem mirror_smul {R : Type _} [Ringₓ R] [IsDomain R] (p : Polynomial R) (a : R) : (a • p).mirror = a • p.mirror :=
  by 
    rw [←C_mul', ←C_mul', mirror_mul_of_domain, mirror_C]

theorem mirror_neg {R : Type _} [Ringₓ R] (p : Polynomial R) : (-p).mirror = -p.mirror :=
  by 
    rw [mirror, mirror, reverse_neg, nat_trailing_degree_neg, neg_mul_eq_neg_mul]

theorem irreducible_of_mirror {R : Type _} [CommRingₓ R] [IsDomain R] {f : Polynomial R} (h1 : ¬IsUnit f)
  (h2 : ∀ k, ((f*f.mirror) = k*k.mirror) → k = f ∨ k = -f ∨ k = f.mirror ∨ k = -f.mirror)
  (h3 : ∀ g, g ∣ f → g ∣ f.mirror → IsUnit g) : Irreducible f :=
  by 
    split 
    ·
      exact h1
    ·
      intro g h fgh 
      let k := g*h.mirror 
      have key : (f*f.mirror) = k*k.mirror
      ·
        rw [fgh, mirror_mul_of_domain, mirror_mul_of_domain, mirror_mirror, mul_assocₓ, mul_commₓ h, mul_commₓ g.mirror,
          mul_assocₓ, ←mul_assocₓ]
      have g_dvd_f : g ∣ f
      ·
        rw [fgh]
        exact dvd_mul_right g h 
      have h_dvd_f : h ∣ f
      ·
        rw [fgh]
        exact dvd_mul_left h g 
      have g_dvd_k : g ∣ k
      ·
        exact dvd_mul_right g h.mirror 
      have h_dvd_k_rev : h ∣ k.mirror
      ·
        rw [mirror_mul_of_domain, mirror_mirror]
        exact dvd_mul_left h g.mirror 
      have hk := h2 k key 
      rcases hk with (hk | hk | hk | hk)
      ·
        exact
          Or.inr
            (h3 h h_dvd_f
              (by 
                rwa [←hk]))
      ·
        exact
          Or.inr
            (h3 h h_dvd_f
              (by 
                rwa [eq_neg_iff_eq_neg.mp hk, mirror_neg, dvd_neg]))
      ·
        exact
          Or.inl
            (h3 g g_dvd_f
              (by 
                rwa [←hk]))
      ·
        exact
          Or.inl
            (h3 g g_dvd_f
              (by 
                rwa [eq_neg_iff_eq_neg.mp hk, dvd_neg]))

end Mirror

end Polynomial

