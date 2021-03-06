/-
Copyright (c) 2020 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker, Devon Tuma
-/
import Mathbin.Analysis.Asymptotics.AsymptoticEquivalent
import Mathbin.Analysis.Asymptotics.SpecificAsymptotics
import Mathbin.Data.Polynomial.RingDivision

/-!
# Limits related to polynomial and rational functions

This file proves basic facts about limits of polynomial and rationals functions.
The main result is `eval_is_equivalent_at_top_eval_lead`, which states that for
any polynomial `P` of degree `n` with leading coefficient `a`, the corresponding
polynomial function is equivalent to `a * x^n` as `x` goes to +โ.

We can then use this result to prove various limits for polynomial and rational
functions, depending on the degrees and leading coefficients of the considered
polynomials.
-/


open Filter Finset Asymptotics

open Asymptotics Polynomial TopologicalSpace

namespace Polynomial

variable {๐ : Type _} [NormedLinearOrderedField ๐] (P Q : ๐[X])

theorem eventually_no_roots (hP : P โ  0) : โแถ  x in at_top, ยฌP.IsRoot x :=
  at_top_le_cofinite <| (finite_set_of_is_root hP).compl_mem_cofinite

variable [OrderTopology ๐]

section PolynomialAtTop

theorem is_equivalent_at_top_lead : (fun x => eval x P) ~[at_top] fun x => P.leadingCoeff * x ^ P.natDegree := by
  by_cases' h : P = 0
  ยท simp [โ h]
    
  ยท conv_rhs => ext rw [Polynomial.eval_eq_sum_range, sum_range_succ]
    exact
      is_equivalent.refl.add_is_o
        (is_o.sum fun i hi =>
          is_o.const_mul_left
            ((is_o.const_mul_right fun hz => h <| leading_coeff_eq_zero.mp hz) <|
              is_o_pow_pow_at_top_of_lt (mem_range.mp hi))
            _)
    

theorem tendsto_at_top_of_leading_coeff_nonneg (hdeg : 0 < P.degree) (hnng : 0 โค P.leadingCoeff) :
    Tendsto (fun x => eval x P) atTop atTop :=
  P.is_equivalent_at_top_lead.symm.tendsto_at_top <|
    tendsto_const_mul_pow_at_top (nat_degree_pos_iff_degree_pos.2 hdeg).ne' <|
      hnng.lt_of_ne' <| leading_coeff_ne_zero.mpr <| ne_zero_of_degree_gt hdeg

theorem tendsto_at_top_iff_leading_coeff_nonneg :
    Tendsto (fun x => eval x P) atTop atTop โ 0 < P.degree โง 0 โค P.leadingCoeff := by
  refine' โจfun h => _, fun h => tendsto_at_top_of_leading_coeff_nonneg P h.1 h.2โฉ
  have : tendsto (fun x => P.leading_coeff * x ^ P.nat_degree) at_top at_top :=
    (is_equivalent_at_top_lead P).tendsto_at_top h
  rw [tendsto_const_mul_pow_at_top_iff, โ pos_iff_ne_zero, nat_degree_pos_iff_degree_pos] at this
  exact โจthis.1, this.2.leโฉ

theorem tendsto_at_bot_iff_leading_coeff_nonpos :
    Tendsto (fun x => eval x P) atTop atBot โ 0 < P.degree โง P.leadingCoeff โค 0 := by
  simp only [tendsto_neg_at_top_iff, eval_neg, โ tendsto_at_top_iff_leading_coeff_nonneg, โ degree_neg, โ
    leading_coeff_neg, โ neg_nonneg]

theorem tendsto_at_bot_of_leading_coeff_nonpos (hdeg : 0 < P.degree) (hnps : P.leadingCoeff โค 0) :
    Tendsto (fun x => eval x P) atTop atBot :=
  P.tendsto_at_bot_iff_leading_coeff_nonpos.2 โจhdeg, hnpsโฉ

theorem abs_tendsto_at_top (hdeg : 0 < P.degree) : Tendsto (fun x => abs <| eval x P) atTop atTop := by
  cases' le_totalโ 0 P.leading_coeff with hP hP
  ยท exact tendsto_abs_at_top_at_top.comp (P.tendsto_at_top_of_leading_coeff_nonneg hdeg hP)
    
  ยท exact tendsto_abs_at_bot_at_top.comp (P.tendsto_at_bot_of_leading_coeff_nonpos hdeg hP)
    

theorem abs_is_bounded_under_iff : (IsBoundedUnder (ยท โค ยท) atTop fun x => abs (eval x P)) โ P.degree โค 0 := by
  refine'
    โจfun h => _, fun h =>
      โจabs (P.coeff 0),
        eventually_map.mpr
          (eventually_of_forall
            (forall_imp (fun _ => le_of_eqโ) fun x =>
              congr_arg abs <| trans (congr_arg (eval x) (eq_C_of_degree_le_zero h)) eval_C))โฉโฉ
  contrapose! h
  exact not_is_bounded_under_of_tendsto_at_top (abs_tendsto_at_top P h)

theorem abs_tendsto_at_top_iff : Tendsto (fun x => abs <| eval x P) atTop atTop โ 0 < P.degree :=
  โจfun h => not_leโ.mp (mt (abs_is_bounded_under_iff P).mpr (not_is_bounded_under_of_tendsto_at_top h)),
    abs_tendsto_at_top Pโฉ

theorem tendsto_nhds_iff {c : ๐} : Tendsto (fun x => eval x P) atTop (๐ c) โ P.leadingCoeff = c โง P.degree โค 0 := by
  refine' โจfun h => _, fun h => _โฉ
  ยท have := P.is_equivalent_at_top_lead.tendsto_nhds h
    by_cases' hP : P.leading_coeff = 0
    ยท simp only [โ hP, โ zero_mul, โ tendsto_const_nhds_iff] at this
      refine'
        โจtrans hP this, by
          simp [โ leading_coeff_eq_zero.1 hP]โฉ
      
    ยท rw [tendsto_const_mul_pow_nhds_iff hP, nat_degree_eq_zero_iff_degree_le_zero] at this
      exact this.symm
      
    
  ยท refine' P.is_equivalent_at_top_lead.symm.tendsto_nhds _
    have : P.nat_degree = 0 := nat_degree_eq_zero_iff_degree_le_zero.2 h.2
    simp only [โ h.1, โ this, โ pow_zeroโ, โ mul_oneโ]
    exact tendsto_const_nhds
    

end PolynomialAtTop

section PolynomialDivAtTop

theorem is_equivalent_at_top_div :
    (fun x => eval x P / eval x Q) ~[at_top] fun x =>
      P.leadingCoeff / Q.leadingCoeff * x ^ (P.natDegree - Q.natDegree : โค) :=
  by
  by_cases' hP : P = 0
  ยท simp [โ hP]
    
  by_cases' hQ : Q = 0
  ยท simp [โ hQ]
    
  refine'
    (P.is_equivalent_at_top_lead.symm.div Q.is_equivalent_at_top_lead.symm).symm.trans
      (eventually_eq.is_equivalent ((eventually_gt_at_top 0).mono fun x hx => _))
  simp [div_mul_div_comm, โ hP, โ hQ, โ zpow_subโ hx.ne.symm]

theorem div_tendsto_zero_of_degree_lt (hdeg : P.degree < Q.degree) :
    Tendsto (fun x => eval x P / eval x Q) atTop (๐ 0) := by
  by_cases' hP : P = 0
  ยท simp [โ hP, โ tendsto_const_nhds]
    
  rw [โ nat_degree_lt_nat_degree_iff hP] at hdeg
  refine' (is_equivalent_at_top_div P Q).symm.tendsto_nhds _
  rw [โ mul_zero]
  refine' (tendsto_zpow_at_top_zero _).const_mul _
  linarith

theorem div_tendsto_zero_iff_degree_lt (hQ : Q โ  0) :
    Tendsto (fun x => eval x P / eval x Q) atTop (๐ 0) โ P.degree < Q.degree := by
  refine' โจfun h => _, div_tendsto_zero_of_degree_lt P Qโฉ
  by_cases' hPQ : P.leading_coeff / Q.leading_coeff = 0
  ยท simp only [โ div_eq_mul_inv, โ inv_eq_zero, โ mul_eq_zero] at hPQ
    cases' hPQ with hP0 hQ0
    ยท rw [leading_coeff_eq_zero.1 hP0, degree_zero]
      exact bot_lt_iff_ne_bot.2 fun hQ' => hQ (degree_eq_bot.1 hQ')
      
    ยท exact absurd (leading_coeff_eq_zero.1 hQ0) hQ
      
    
  ยท have := (is_equivalent_at_top_div P Q).tendsto_nhds h
    rw [tendsto_const_mul_zpow_at_top_nhds_iff hPQ] at this
    cases' this with h h
    ยท exact absurd h.2 hPQ
      
    ยท rw [sub_lt_iff_lt_add, zero_addโ, Int.coe_nat_lt] at h
      exact degree_lt_degree h.1
      
    

theorem div_tendsto_leading_coeff_div_of_degree_eq (hdeg : P.degree = Q.degree) :
    Tendsto (fun x => eval x P / eval x Q) atTop (๐ <| P.leadingCoeff / Q.leadingCoeff) := by
  refine' (is_equivalent_at_top_div P Q).symm.tendsto_nhds _
  rw
    [show (P.nat_degree : โค) = Q.nat_degree by
      simp [โ hdeg, โ nat_degree]]
  simp [โ tendsto_const_nhds]

theorem div_tendsto_at_top_of_degree_gt' (hdeg : Q.degree < P.degree) (hpos : 0 < P.leadingCoeff / Q.leadingCoeff) :
    Tendsto (fun x => eval x P / eval x Q) atTop atTop := by
  have hQ : Q โ  0 := fun h => by
    simp only [โ h, โ div_zero, โ leading_coeff_zero] at hpos
    linarith
  rw [โ nat_degree_lt_nat_degree_iff hQ] at hdeg
  refine' (is_equivalent_at_top_div P Q).symm.tendsto_at_top _
  apply tendsto.const_mul_at_top hpos
  apply tendsto_zpow_at_top_at_top
  linarith

theorem div_tendsto_at_top_of_degree_gt (hdeg : Q.degree < P.degree) (hQ : Q โ  0)
    (hnng : 0 โค P.leadingCoeff / Q.leadingCoeff) : Tendsto (fun x => eval x P / eval x Q) atTop atTop :=
  have ratio_pos : 0 < P.leadingCoeff / Q.leadingCoeff :=
    lt_of_le_of_neโ hnng
      (div_ne_zero (fun h => ne_zero_of_degree_gt hdeg <| leading_coeff_eq_zero.mp h) fun h =>
          hQ <| leading_coeff_eq_zero.mp h).symm
  div_tendsto_at_top_of_degree_gt' P Q hdeg ratio_pos

theorem div_tendsto_at_bot_of_degree_gt' (hdeg : Q.degree < P.degree) (hneg : P.leadingCoeff / Q.leadingCoeff < 0) :
    Tendsto (fun x => eval x P / eval x Q) atTop atBot := by
  have hQ : Q โ  0 := fun h => by
    simp only [โ h, โ div_zero, โ leading_coeff_zero] at hneg
    linarith
  rw [โ nat_degree_lt_nat_degree_iff hQ] at hdeg
  refine' (is_equivalent_at_top_div P Q).symm.tendsto_at_bot _
  apply tendsto.neg_const_mul_at_top hneg
  apply tendsto_zpow_at_top_at_top
  linarith

theorem div_tendsto_at_bot_of_degree_gt (hdeg : Q.degree < P.degree) (hQ : Q โ  0)
    (hnps : P.leadingCoeff / Q.leadingCoeff โค 0) : Tendsto (fun x => eval x P / eval x Q) atTop atBot :=
  have ratio_neg : P.leadingCoeff / Q.leadingCoeff < 0 :=
    lt_of_le_of_neโ hnps
      (div_ne_zero (fun h => ne_zero_of_degree_gt hdeg <| leading_coeff_eq_zero.mp h) fun h =>
        hQ <| leading_coeff_eq_zero.mp h)
  div_tendsto_at_bot_of_degree_gt' P Q hdeg ratio_neg

theorem abs_div_tendsto_at_top_of_degree_gt (hdeg : Q.degree < P.degree) (hQ : Q โ  0) :
    Tendsto (fun x => abs (eval x P / eval x Q)) atTop atTop := by
  by_cases' h : 0 โค P.leading_coeff / Q.leading_coeff
  ยท exact tendsto_abs_at_top_at_top.comp (P.div_tendsto_at_top_of_degree_gt Q hdeg hQ h)
    
  ยท push_neg  at h
    exact tendsto_abs_at_bot_at_top.comp (P.div_tendsto_at_bot_of_degree_gt Q hdeg hQ h.le)
    

end PolynomialDivAtTop

theorem is_O_of_degree_le (h : P.degree โค Q.degree) : (fun x => eval x P) =O[at_top] fun x => eval x Q := by
  by_cases' hp : P = 0
  ยท simpa [โ hp] using is_O_zero (fun x => eval x Q) at_top
    
  ยท have hq : Q โ  0 := ne_zero_of_degree_ge_degree h hp
    have hPQ : โแถ  x : ๐ in at_top, eval x Q = 0 โ eval x P = 0 :=
      Filter.mem_of_superset (Polynomial.eventually_no_roots Q hq) fun x h h' => absurd h' h
    cases' le_iff_lt_or_eq.mp h with h h
    ยท exact is_O_of_div_tendsto_nhds hPQ 0 (div_tendsto_zero_of_degree_lt P Q h)
      
    ยท exact is_O_of_div_tendsto_nhds hPQ _ (div_tendsto_leading_coeff_div_of_degree_eq P Q h)
      
    

end Polynomial

