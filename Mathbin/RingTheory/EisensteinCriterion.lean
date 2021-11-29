import Mathbin.RingTheory.Prime 
import Mathbin.RingTheory.Polynomial.Content

/-!
# Eisenstein's criterion

A proof of a slight generalisation of Eisenstein's criterion for the irreducibility of
a polynomial over an integral domain.
-/


open Polynomial Ideal.Quotient

variable{R : Type _}[CommRingₓ R]

namespace Polynomial

namespace EisensteinCriterionAux

-- error in RingTheory.EisensteinCriterion: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem map_eq_C_mul_X_pow_of_forall_coeff_mem
{f : polynomial R}
{P : ideal R}
(hfP : ∀ n : exprℕ(), «expr < »(«expr↑ »(n), f.degree) → «expr ∈ »(f.coeff n, P))
(hf0 : «expr ≠ »(f, 0)) : «expr = »(map (mk P) f, «expr * »(C (mk P f.leading_coeff), «expr ^ »(X, f.nat_degree))) :=
polynomial.ext (λ n, begin
   rcases [expr lt_trichotomy «expr↑ »(n) (degree f), "with", ident h, "|", ident h, "|", ident h],
   { erw ["[", expr coeff_map, ",", expr eq_zero_iff_mem.2 (hfP n h), ",", expr coeff_C_mul, ",", expr coeff_X_pow, ",", expr if_neg, ",", expr mul_zero, "]"] [],
     rintro [ident rfl],
     exact [expr not_lt_of_ge degree_le_nat_degree h] },
   { have [] [":", expr «expr = »(nat_degree f, n)] [],
     from [expr nat_degree_eq_of_degree_eq_some h.symm],
     rw ["[", expr coeff_C_mul, ",", expr coeff_X_pow, ",", expr if_pos this.symm, ",", expr mul_one, ",", expr leading_coeff, ",", expr this, ",", expr coeff_map, "]"] [] },
   { rw ["[", expr coeff_eq_zero_of_degree_lt, ",", expr coeff_eq_zero_of_degree_lt, "]"] [],
     { refine [expr lt_of_le_of_lt (degree_C_mul_X_pow_le _ _) _],
       rwa ["<-", expr degree_eq_nat_degree hf0] [] },
     { exact [expr lt_of_le_of_lt (degree_map_le _ _) h] } }
 end)

theorem le_nat_degree_of_map_eq_mul_X_pow {n : ℕ} {P : Ideal R} (hP : P.is_prime) {q : Polynomial R}
  {c : Polynomial P.quotient} (hq : map (mk P) q = c*X ^ n) (hc0 : c.degree = 0) : n ≤ q.nat_degree :=
  WithBot.coe_le_coe.1
    (calc «expr↑ » n = degree (q.map (mk P)) :=
      by 
        rw [hq, degree_mul, hc0, zero_addₓ, degree_pow, degree_X, nsmul_one, Nat.cast_with_bot]
      _ ≤ degree q := degree_map_le _ _ 
      _ ≤ nat_degree q := degree_le_nat_degree
      )

theorem eval_zero_mem_ideal_of_eq_mul_X_pow {n : ℕ} {P : Ideal R} {q : Polynomial R} {c : Polynomial P.quotient}
  (hq : map (mk P) q = c*X ^ n) (hn0 : 0 < n) : eval 0 q ∈ P :=
  by 
    rw [←coeff_zero_eq_eval_zero, ←eq_zero_iff_mem, ←coeff_map, coeff_zero_eq_eval_zero, hq, eval_mul, eval_pow, eval_X,
      zero_pow hn0, mul_zero]

theorem is_unit_of_nat_degree_eq_zero_of_forall_dvd_is_unit {p q : Polynomial R}
  (hu : ∀ (x : R), (C x ∣ p*q) → IsUnit x) (hpm : p.nat_degree = 0) : IsUnit p :=
  by 
    rw [eq_C_of_degree_le_zero (nat_degree_eq_zero_iff_degree_le_zero.1 hpm), is_unit_C]
    refine' hu _ _ 
    rw [←eq_C_of_degree_le_zero (nat_degree_eq_zero_iff_degree_le_zero.1 hpm)]
    exact dvd_mul_right _ _

end EisensteinCriterionAux

open EisensteinCriterionAux

variable[IsDomain R]

-- error in RingTheory.EisensteinCriterion: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- If `f` is a non constant polynomial with coefficients in `R`, and `P` is a prime ideal in `R`,
then if every coefficient in `R` except the leading coefficient is in `P`, and
the trailing coefficient is not in `P^2` and no non units in `R` divide `f`, then `f` is
irreducible. -/
theorem irreducible_of_eisenstein_criterion
{f : polynomial R}
{P : ideal R}
(hP : P.is_prime)
(hfl : «expr ∉ »(f.leading_coeff, P))
(hfP : ∀ n : exprℕ(), «expr < »(«expr↑ »(n), degree f) → «expr ∈ »(f.coeff n, P))
(hfd0 : «expr < »(0, degree f))
(h0 : «expr ∉ »(f.coeff 0, «expr ^ »(P, 2)))
(hu : f.is_primitive) : irreducible f :=
have hf0 : «expr ≠ »(f, 0), from λ
_, by simp [] [] ["only"] ["[", "*", ",", expr not_true, ",", expr submodule.zero_mem, ",", expr coeff_zero, "]"] [] ["at", "*"],
have hf : «expr = »(f.map (mk P), «expr * »(C (mk P (leading_coeff f)), «expr ^ »(X, nat_degree f))), from map_eq_C_mul_X_pow_of_forall_coeff_mem hfP hf0,
have hfd0 : «expr < »(0, f.nat_degree), from with_bot.coe_lt_coe.1 (lt_of_lt_of_le hfd0 degree_le_nat_degree),
⟨mt degree_eq_zero_of_is_unit (λ h, by simp [] [] ["only"] ["[", "*", ",", expr lt_irrefl, "]"] [] ["at", "*"]), begin
   rintros [ident p, ident q, ident rfl],
   rw ["[", expr map_mul, "]"] ["at", ident hf],
   rcases [expr mul_eq_mul_prime_pow (show prime (X : polynomial (ideal.quotient P)), from monic_X.prime_of_degree_eq_one degree_X) hf, "with", "⟨", ident m, ",", ident n, ",", ident b, ",", ident c, ",", ident hmnd, ",", ident hbc, ",", ident hp, ",", ident hq, "⟩"],
   have [ident hmn] [":", expr «expr < »(0, m) → «expr < »(0, n) → false] [],
   { assume [binders (hm0 hn0)],
     refine [expr h0 _],
     rw ["[", expr coeff_zero_eq_eval_zero, ",", expr eval_mul, ",", expr sq, "]"] [],
     exact [expr ideal.mul_mem_mul (eval_zero_mem_ideal_of_eq_mul_X_pow hp hm0) (eval_zero_mem_ideal_of_eq_mul_X_pow hq hn0)] },
   have [ident hpql0] [":", expr «expr ≠ »(mk P «expr * »(p, q).leading_coeff, 0)] [],
   { rwa ["[", expr ne.def, ",", expr eq_zero_iff_mem, "]"] [] },
   have [ident hp0] [":", expr «expr ≠ »(p, 0)] [],
   from [expr λ
    h, by simp [] [] ["only"] ["[", "*", ",", expr zero_mul, ",", expr eq_self_iff_true, ",", expr not_true, ",", expr ne.def, "]"] [] ["at", "*"]],
   have [ident hq0] [":", expr «expr ≠ »(q, 0)] [],
   from [expr λ
    h, by simp [] [] ["only"] ["[", "*", ",", expr eq_self_iff_true, ",", expr not_true, ",", expr ne.def, ",", expr mul_zero, "]"] [] ["at", "*"]],
   have [ident hbc0] [":", expr «expr ∧ »(«expr = »(degree b, 0), «expr = »(degree c, 0))] [],
   { apply_fun [expr degree] ["at", ident hbc] [],
     rwa ["[", expr degree_C hpql0, ",", expr degree_mul, ",", expr eq_comm, ",", expr nat.with_bot.add_eq_zero_iff, "]"] ["at", ident hbc] },
   have [ident hmp] [":", expr «expr ≤ »(m, nat_degree p)] [],
   from [expr le_nat_degree_of_map_eq_mul_X_pow hP hp hbc0.1],
   have [ident hnq] [":", expr «expr ≤ »(n, nat_degree q)] [],
   from [expr le_nat_degree_of_map_eq_mul_X_pow hP hq hbc0.2],
   have [ident hpmqn] [":", expr «expr ∧ »(«expr = »(p.nat_degree, m), «expr = »(q.nat_degree, n))] [],
   { rw ["[", expr nat_degree_mul hp0 hq0, "]"] ["at", ident hmnd],
     clear_except [ident hmnd, ident hmp, ident hnq],
     contrapose [] [ident hmnd],
     apply [expr ne_of_lt],
     rw [expr not_and_distrib] ["at", ident hmnd],
     cases [expr hmnd] [],
     { exact [expr add_lt_add_of_lt_of_le (lt_of_le_of_ne hmp (ne.symm hmnd)) hnq] },
     { exact [expr add_lt_add_of_le_of_lt hmp (lt_of_le_of_ne hnq (ne.symm hmnd))] } },
   obtain [ident rfl, "|", ident rfl, ":", expr «expr ∨ »(«expr = »(m, 0), «expr = »(n, 0))],
   { rwa ["[", expr pos_iff_ne_zero, ",", expr pos_iff_ne_zero, ",", expr imp_false, ",", expr not_not, ",", "<-", expr or_iff_not_imp_left, "]"] ["at", ident hmn] },
   { exact [expr or.inl (is_unit_of_nat_degree_eq_zero_of_forall_dvd_is_unit hu hpmqn.1)] },
   { exact [expr or.inr (is_unit_of_nat_degree_eq_zero_of_forall_dvd_is_unit (by simpa [] [] ["only"] ["[", expr mul_comm, "]"] [] ["using", expr hu]) hpmqn.2)] }
 end⟩

end Polynomial

