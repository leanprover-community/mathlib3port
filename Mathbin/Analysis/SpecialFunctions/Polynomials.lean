import Mathbin.Analysis.Asymptotics.AsymptoticEquivalent 
import Mathbin.Analysis.Asymptotics.SpecificAsymptotics 
import Mathbin.Data.Polynomial.RingDivision

/-!
# Limits related to polynomial and rational functions

This file proves basic facts about limits of polynomial and rationals functions.
The main result is `eval_is_equivalent_at_top_eval_lead`, which states that for
any polynomial `P` of degree `n` with leading coefficient `a`, the corresponding
polynomial function is equivalent to `a * x^n` as `x` goes to +∞.

We can then use this result to prove various limits for polynomial and rational
functions, depending on the degrees and leading coefficients of the considered
polynomials.
-/


open Filter Finset Asymptotics

open_locale Asymptotics TopologicalSpace

namespace Polynomial

variable {𝕜 : Type _} [NormedLinearOrderedField 𝕜] (P Q : Polynomial 𝕜)

theorem eventually_no_roots (hP : P ≠ 0) : ∀ᶠx in Filter.atTop, ¬P.is_root x :=
  by 
    obtain ⟨x₀, hx₀⟩ := exists_max_root P hP 
    refine' filter.eventually_at_top.mpr ⟨x₀+1, fun x hx h => _⟩
    exact absurd (hx₀ x h) (not_le.mpr (lt_of_lt_of_leₓ (lt_add_one x₀) hx))

variable [OrderTopology 𝕜]

section PolynomialAtTop

theorem is_equivalent_at_top_lead : (fun x => eval x P) ~[at_top] fun x => P.leading_coeff*x ^ P.nat_degree :=
  by 
    byCases' h : P = 0
    ·
      simp [h]
    ·
      convLHS => ext rw [Polynomial.eval_eq_finset_sum, sum_range_succ]
      exact
        is_equivalent.refl.add_is_o
          (is_o.sum$
            fun i hi =>
              is_o.const_mul_left
                ((is_o.const_mul_right fun hz => h$ leading_coeff_eq_zero.mp hz)$
                  is_o_pow_pow_at_top_of_lt (mem_range.mp hi))
                _)

theorem tendsto_at_top_of_leading_coeff_nonneg (hdeg : 1 ≤ P.degree) (hnng : 0 ≤ P.leading_coeff) :
  tendsto (fun x => eval x P) at_top at_top :=
  P.is_equivalent_at_top_lead.symm.tendsto_at_top
    (tendsto_const_mul_pow_at_top (le_nat_degree_of_coe_le_degree hdeg)
      (lt_of_le_of_neₓ hnng$ Ne.symm$ mt leading_coeff_eq_zero.mp$ ne_zero_of_coe_le_degree hdeg))

-- error in Analysis.SpecialFunctions.Polynomials: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem tendsto_at_top_iff_leading_coeff_nonneg : «expr ↔ »(tendsto (λ
  x, eval x P) at_top at_top, «expr ∧ »(«expr ≤ »(1, P.degree), «expr ≤ »(0, P.leading_coeff))) :=
begin
  refine [expr ⟨λ h, _, λ h, tendsto_at_top_of_leading_coeff_nonneg P h.1 h.2⟩],
  have [] [":", expr tendsto (λ
    x, «expr * »(P.leading_coeff, «expr ^ »(x, P.nat_degree))) at_top at_top] [":=", expr is_equivalent.tendsto_at_top (is_equivalent_at_top_lead P) h],
  rw [expr tendsto_const_mul_pow_at_top_iff P.leading_coeff P.nat_degree] ["at", ident this],
  rw ["[", expr degree_eq_nat_degree (leading_coeff_ne_zero.mp (ne_of_lt this.2).symm), ",", "<-", expr nat.cast_one, "]"] [],
  refine [expr ⟨with_bot.coe_le_coe.mpr this.1, le_of_lt this.2⟩]
end

theorem tendsto_at_bot_of_leading_coeff_nonpos (hdeg : 1 ≤ P.degree) (hnps : P.leading_coeff ≤ 0) :
  tendsto (fun x => eval x P) at_top at_bot :=
  P.is_equivalent_at_top_lead.symm.tendsto_at_bot
    (tendsto_neg_const_mul_pow_at_top (le_nat_degree_of_coe_le_degree hdeg)
      (lt_of_le_of_neₓ hnps$ mt leading_coeff_eq_zero.mp$ ne_zero_of_coe_le_degree hdeg))

-- error in Analysis.SpecialFunctions.Polynomials: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem tendsto_at_bot_iff_leading_coeff_nonpos : «expr ↔ »(tendsto (λ
  x, eval x P) at_top at_bot, «expr ∧ »(«expr ≤ »(1, P.degree), «expr ≤ »(P.leading_coeff, 0))) :=
begin
  refine [expr ⟨λ h, _, λ h, tendsto_at_bot_of_leading_coeff_nonpos P h.1 h.2⟩],
  have [] [":", expr tendsto (λ
    x, «expr * »(P.leading_coeff, «expr ^ »(x, P.nat_degree))) at_top at_bot] [":=", expr is_equivalent.tendsto_at_bot (is_equivalent_at_top_lead P) h],
  rw [expr tendsto_neg_const_mul_pow_at_top_iff P.leading_coeff P.nat_degree] ["at", ident this],
  rw ["[", expr degree_eq_nat_degree (leading_coeff_ne_zero.mp (ne_of_lt this.2)), ",", "<-", expr nat.cast_one, "]"] [],
  refine [expr ⟨with_bot.coe_le_coe.mpr this.1, le_of_lt this.2⟩]
end

theorem abs_tendsto_at_top (hdeg : 1 ≤ P.degree) : tendsto (fun x => abs$ eval x P) at_top at_top :=
  by 
    byCases' hP : 0 ≤ P.leading_coeff
    ·
      exact tendsto_abs_at_top_at_top.comp (P.tendsto_at_top_of_leading_coeff_nonneg hdeg hP)
    ·
      pushNeg  at hP 
      exact tendsto_abs_at_bot_at_top.comp (P.tendsto_at_bot_of_leading_coeff_nonpos hdeg hP.le)

theorem abs_is_bounded_under_iff : (is_bounded_under (· ≤ ·) at_top fun x => |eval x P|) ↔ P.degree ≤ 0 :=
  by 
    refine'
      ⟨fun h => _,
        fun h =>
          ⟨|P.coeff 0|,
            eventually_map.mpr
              (eventually_of_forall
                (forall_imp (fun _ => le_of_eqₓ)
                  fun x => congr_argₓ abs$ trans (congr_argₓ (eval x) (eq_C_of_degree_le_zero h)) eval_C))⟩⟩
    contrapose! h 
    exact not_is_bounded_under_of_tendsto_at_top (abs_tendsto_at_top P (Nat.WithBot.one_le_iff_zero_lt.2 h))

theorem abs_tendsto_at_top_iff : tendsto (fun x => abs$ eval x P) at_top at_top ↔ 1 ≤ P.degree :=
  ⟨fun h =>
      Nat.WithBot.one_le_iff_zero_lt.2
        (not_leₓ.mp ((mt (abs_is_bounded_under_iff P).mpr) (not_is_bounded_under_of_tendsto_at_top h))),
    abs_tendsto_at_top P⟩

-- error in Analysis.SpecialFunctions.Polynomials: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem tendsto_nhds_iff
{c : 𝕜} : «expr ↔ »(tendsto (λ
  x, eval x P) at_top (expr𝓝() c), «expr ∧ »(«expr = »(P.leading_coeff, c), «expr ≤ »(P.degree, 0))) :=
begin
  refine [expr ⟨λ h, _, λ h, _⟩],
  { have [] [] [":=", expr P.is_equivalent_at_top_lead.tendsto_nhds h],
    by_cases [expr hP, ":", expr «expr = »(P.leading_coeff, 0)],
    { simp [] [] ["only"] ["[", expr hP, ",", expr zero_mul, ",", expr tendsto_const_nhds_iff, "]"] [] ["at", ident this],
      refine [expr ⟨trans hP this, by simp [] [] [] ["[", expr leading_coeff_eq_zero.1 hP, "]"] [] []⟩] },
    { rw ["[", expr tendsto_const_mul_pow_nhds_iff hP, ",", expr nat_degree_eq_zero_iff_degree_le_zero, "]"] ["at", ident this],
      exact [expr this.symm] } },
  { refine [expr P.is_equivalent_at_top_lead.symm.tendsto_nhds _],
    have [] [":", expr «expr = »(P.nat_degree, 0)] [":=", expr nat_degree_eq_zero_iff_degree_le_zero.2 h.2],
    simp [] [] ["only"] ["[", expr h.1, ",", expr this, ",", expr pow_zero, ",", expr mul_one, "]"] [] [],
    exact [expr tendsto_const_nhds] }
end

end PolynomialAtTop

section PolynomialDivAtTop

theorem is_equivalent_at_top_div :
  (fun x => eval x P / eval x Q) ~[at_top]
    fun x => (P.leading_coeff / Q.leading_coeff)*x ^ (P.nat_degree - Q.nat_degree : ℤ) :=
  by 
    byCases' hP : P = 0
    ·
      simp [hP]
    byCases' hQ : Q = 0
    ·
      simp [hQ]
    refine'
      (P.is_equivalent_at_top_lead.symm.div Q.is_equivalent_at_top_lead.symm).symm.trans
        (eventually_eq.is_equivalent ((eventually_gt_at_top 0).mono$ fun x hx => _))
    simp [←div_mul_div, hP, hQ, zpow_sub₀ hx.ne.symm]

theorem div_tendsto_zero_of_degree_lt (hdeg : P.degree < Q.degree) :
  tendsto (fun x => eval x P / eval x Q) at_top (𝓝 0) :=
  by 
    byCases' hP : P = 0
    ·
      simp [hP, tendsto_const_nhds]
    rw [←nat_degree_lt_nat_degree_iff hP] at hdeg 
    refine' (is_equivalent_at_top_div P Q).symm.tendsto_nhds _ 
    rw [←mul_zero]
    refine' (tendsto_zpow_at_top_zero _).const_mul _ 
    linarith

-- error in Analysis.SpecialFunctions.Polynomials: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem div_tendsto_zero_iff_degree_lt
(hQ : «expr ≠ »(Q, 0)) : «expr ↔ »(tendsto (λ
  x, «expr / »(eval x P, eval x Q)) at_top (expr𝓝() 0), «expr < »(P.degree, Q.degree)) :=
begin
  refine [expr ⟨λ h, _, div_tendsto_zero_of_degree_lt P Q⟩],
  by_cases [expr hPQ, ":", expr «expr = »(«expr / »(P.leading_coeff, Q.leading_coeff), 0)],
  { simp [] [] ["only"] ["[", expr div_eq_mul_inv, ",", expr inv_eq_zero, ",", expr mul_eq_zero, "]"] [] ["at", ident hPQ],
    cases [expr hPQ] ["with", ident hP0, ident hQ0],
    { rw ["[", expr leading_coeff_eq_zero.1 hP0, ",", expr degree_zero, "]"] [],
      exact [expr bot_lt_iff_ne_bot.2 (λ hQ', hQ (degree_eq_bot.1 hQ'))] },
    { exact [expr absurd (leading_coeff_eq_zero.1 hQ0) hQ] } },
  { have [] [] [":=", expr (is_equivalent_at_top_div P Q).tendsto_nhds h],
    rw [expr tendsto_const_mul_zpow_at_top_zero_iff hPQ] ["at", ident this],
    cases [expr this] ["with", ident h, ident h],
    { exact [expr absurd h.2 hPQ] },
    { rw ["[", expr sub_lt_iff_lt_add, ",", expr zero_add, ",", expr int.coe_nat_lt, "]"] ["at", ident h],
      exact [expr degree_lt_degree h.1] } }
end

theorem div_tendsto_leading_coeff_div_of_degree_eq (hdeg : P.degree = Q.degree) :
  tendsto (fun x => eval x P / eval x Q) at_top (𝓝$ P.leading_coeff / Q.leading_coeff) :=
  by 
    refine' (is_equivalent_at_top_div P Q).symm.tendsto_nhds _ 
    rw
      [show (P.nat_degree : ℤ) = Q.nat_degree by 
        simp [hdeg, nat_degree]]
    simp [tendsto_const_nhds]

-- error in Analysis.SpecialFunctions.Polynomials: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem div_tendsto_at_top_of_degree_gt'
(hdeg : «expr < »(Q.degree, P.degree))
(hpos : «expr < »(0, «expr / »(P.leading_coeff, Q.leading_coeff))) : tendsto (λ
 x, «expr / »(eval x P, eval x Q)) at_top at_top :=
begin
  have [ident hQ] [":", expr «expr ≠ »(Q, 0)] [":=", expr λ
   h, by { simp [] [] ["only"] ["[", expr h, ",", expr div_zero, ",", expr leading_coeff_zero, "]"] [] ["at", ident hpos],
     linarith [] [] [] }],
  rw ["<-", expr nat_degree_lt_nat_degree_iff hQ] ["at", ident hdeg],
  refine [expr (is_equivalent_at_top_div P Q).symm.tendsto_at_top _],
  apply [expr tendsto.const_mul_at_top hpos],
  apply [expr tendsto_zpow_at_top_at_top],
  linarith [] [] []
end

theorem div_tendsto_at_top_of_degree_gt (hdeg : Q.degree < P.degree) (hQ : Q ≠ 0)
  (hnng : 0 ≤ P.leading_coeff / Q.leading_coeff) : tendsto (fun x => eval x P / eval x Q) at_top at_top :=
  have ratio_pos : 0 < P.leading_coeff / Q.leading_coeff :=
    lt_of_le_of_neₓ hnng
      (div_ne_zero (fun h => ne_zero_of_degree_gt hdeg$ leading_coeff_eq_zero.mp h)
          fun h => hQ$ leading_coeff_eq_zero.mp h).symm
        
  div_tendsto_at_top_of_degree_gt' P Q hdeg ratio_pos

-- error in Analysis.SpecialFunctions.Polynomials: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem div_tendsto_at_bot_of_degree_gt'
(hdeg : «expr < »(Q.degree, P.degree))
(hneg : «expr < »(«expr / »(P.leading_coeff, Q.leading_coeff), 0)) : tendsto (λ
 x, «expr / »(eval x P, eval x Q)) at_top at_bot :=
begin
  have [ident hQ] [":", expr «expr ≠ »(Q, 0)] [":=", expr λ
   h, by { simp [] [] ["only"] ["[", expr h, ",", expr div_zero, ",", expr leading_coeff_zero, "]"] [] ["at", ident hneg],
     linarith [] [] [] }],
  rw ["<-", expr nat_degree_lt_nat_degree_iff hQ] ["at", ident hdeg],
  refine [expr (is_equivalent_at_top_div P Q).symm.tendsto_at_bot _],
  apply [expr tendsto.neg_const_mul_at_top hneg],
  apply [expr tendsto_zpow_at_top_at_top],
  linarith [] [] []
end

theorem div_tendsto_at_bot_of_degree_gt (hdeg : Q.degree < P.degree) (hQ : Q ≠ 0)
  (hnps : P.leading_coeff / Q.leading_coeff ≤ 0) : tendsto (fun x => eval x P / eval x Q) at_top at_bot :=
  have ratio_neg : P.leading_coeff / Q.leading_coeff < 0 :=
    lt_of_le_of_neₓ hnps
      (div_ne_zero (fun h => ne_zero_of_degree_gt hdeg$ leading_coeff_eq_zero.mp h)
        fun h => hQ$ leading_coeff_eq_zero.mp h)
  div_tendsto_at_bot_of_degree_gt' P Q hdeg ratio_neg

theorem abs_div_tendsto_at_top_of_degree_gt (hdeg : Q.degree < P.degree) (hQ : Q ≠ 0) :
  tendsto (fun x => |eval x P / eval x Q|) at_top at_top :=
  by 
    byCases' h : 0 ≤ P.leading_coeff / Q.leading_coeff
    ·
      exact tendsto_abs_at_top_at_top.comp (P.div_tendsto_at_top_of_degree_gt Q hdeg hQ h)
    ·
      pushNeg  at h 
      exact tendsto_abs_at_bot_at_top.comp (P.div_tendsto_at_bot_of_degree_gt Q hdeg hQ h.le)

end PolynomialDivAtTop

-- error in Analysis.SpecialFunctions.Polynomials: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem is_O_of_degree_le (h : «expr ≤ »(P.degree, Q.degree)) : is_O (λ x, eval x P) (λ x, eval x Q) filter.at_top :=
begin
  by_cases [expr hp, ":", expr «expr = »(P, 0)],
  { simpa [] [] [] ["[", expr hp, "]"] [] ["using", expr is_O_zero (λ x, eval x Q) filter.at_top] },
  { have [ident hq] [":", expr «expr ≠ »(Q, 0)] [":=", expr ne_zero_of_degree_ge_degree h hp],
    have [ident hPQ] [":", expr «expr∀ᶠ in , »((x : 𝕜), at_top, «expr = »(eval x Q, 0) → «expr = »(eval x P, 0))] [":=", expr filter.mem_of_superset (polynomial.eventually_no_roots Q hq) (λ
      x h h', absurd h' h)],
    cases [expr le_iff_lt_or_eq.mp h] ["with", ident h, ident h],
    { exact [expr is_O_of_div_tendsto_nhds hPQ 0 (div_tendsto_zero_of_degree_lt P Q h)] },
    { exact [expr is_O_of_div_tendsto_nhds hPQ _ (div_tendsto_leading_coeff_div_of_degree_eq P Q h)] } }
end

end Polynomial

