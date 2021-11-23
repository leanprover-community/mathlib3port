import Mathbin.Data.Polynomial.Degree.Definitions

/-!
# Cancel the leading terms of two polynomials

## Definition

* `cancel_leads p q`: the polynomial formed by multiplying `p` and `q` by monomials so that they
  have the same leading term, and then subtracting.

## Main Results
The degree of `cancel_leads` is less than that of the larger of the two polynomials being cancelled.
Thus it is useful for induction or minimal-degree arguments.
-/


namespace Polynomial

noncomputable theory

variable{R : Type _}

section CommRingₓ

variable[CommRingₓ R](p q : Polynomial R)

/-- `cancel_leads p q` is formed by multiplying `p` and `q` by monomials so that they
  have the same leading term, and then subtracting. -/
def cancel_leads : Polynomial R :=
  ((C p.leading_coeff*X ^ (p.nat_degree - q.nat_degree))*q) - (C q.leading_coeff*X ^ (q.nat_degree - p.nat_degree))*p

variable{p q}

@[simp]
theorem neg_cancel_leads : -p.cancel_leads q = q.cancel_leads p :=
  neg_sub _ _

theorem dvd_cancel_leads_of_dvd_of_dvd {r : Polynomial R} (pq : p ∣ q) (pr : p ∣ r) : p ∣ q.cancel_leads r :=
  dvd_sub (pr.trans (Dvd.intro_left _ rfl)) (pq.trans (Dvd.intro_left _ rfl))

end CommRingₓ

-- error in Data.Polynomial.CancelLeads: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem nat_degree_cancel_leads_lt_of_nat_degree_le_nat_degree
[comm_ring R]
[is_domain R]
{p q : polynomial R}
(h : «expr ≤ »(p.nat_degree, q.nat_degree))
(hq : «expr < »(0, q.nat_degree)) : «expr < »((p.cancel_leads q).nat_degree, q.nat_degree) :=
begin
  by_cases [expr hp, ":", expr «expr = »(p, 0)],
  { convert [] [expr hq] [],
    simp [] [] [] ["[", expr hp, ",", expr cancel_leads, "]"] [] [] },
  rw ["[", expr cancel_leads, ",", expr sub_eq_add_neg, ",", expr tsub_eq_zero_iff_le.mpr h, ",", expr pow_zero, ",", expr mul_one, "]"] [],
  by_cases [expr h0, ":", expr «expr = »(«expr + »(«expr * »(C p.leading_coeff, q), «expr- »(«expr * »(«expr * »(C q.leading_coeff, «expr ^ »(X, «expr - »(q.nat_degree, p.nat_degree))), p))), 0)],
  { convert [] [expr hq] [],
    simp [] [] ["only"] ["[", expr h0, ",", expr nat_degree_zero, "]"] [] [] },
  have [ident hq0] [":", expr «expr¬ »(«expr = »(q, 0))] [],
  { contrapose ["!"] [ident hq],
    simp [] [] [] ["[", expr hq, "]"] [] [] },
  apply [expr lt_of_le_of_ne],
  { rw ["[", "<-", expr with_bot.coe_le_coe, ",", "<-", expr degree_eq_nat_degree h0, ",", "<-", expr degree_eq_nat_degree hq0, "]"] [],
    apply [expr le_trans (degree_add_le _ _)],
    rw ["<-", expr leading_coeff_eq_zero] ["at", ident hp, ident hq0],
    simp [] [] ["only"] ["[", expr max_le_iff, ",", expr degree_C hp, ",", expr degree_C hq0, ",", expr le_refl q.degree, ",", expr true_and, ",", expr nat.cast_with_bot, ",", expr nsmul_one, ",", expr degree_neg, ",", expr degree_mul, ",", expr zero_add, ",", expr degree_X, ",", expr degree_pow, "]"] [] [],
    rw [expr leading_coeff_eq_zero] ["at", ident hp, ident hq0],
    rw ["[", expr degree_eq_nat_degree hp, ",", expr degree_eq_nat_degree hq0, ",", "<-", expr with_bot.coe_add, ",", expr with_bot.coe_le_coe, ",", expr tsub_add_cancel_of_le h, "]"] [] },
  { contrapose ["!"] [ident h0],
    rw ["[", "<-", expr leading_coeff_eq_zero, ",", expr leading_coeff, ",", expr h0, ",", expr mul_assoc, ",", expr mul_comm _ p, ",", "<-", expr tsub_add_cancel_of_le h, ",", expr add_comm _ p.nat_degree, "]"] [],
    simp [] [] ["only"] ["[", expr coeff_mul_X_pow, ",", expr coeff_neg, ",", expr coeff_C_mul, ",", expr add_tsub_cancel_left, ",", expr coeff_add, "]"] [] [],
    rw ["[", expr add_comm p.nat_degree, ",", expr tsub_add_cancel_of_le h, ",", "<-", expr leading_coeff, ",", "<-", expr leading_coeff, ",", expr mul_comm _ q.leading_coeff, ",", "<-", expr sub_eq_add_neg, ",", "<-", expr mul_sub, ",", expr sub_self, ",", expr mul_zero, "]"] [] }
end

end Polynomial

