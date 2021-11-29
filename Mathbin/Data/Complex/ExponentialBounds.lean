import Mathbin.Data.Complex.Exponential 
import Mathbin.Analysis.SpecialFunctions.LogDeriv

/-!
# Bounds on specific values of the exponential
-/


namespace Real

open IsAbsoluteValue Finset CauSeq Complex

theorem exp_one_near_10 : |exp 1 - 2244083 / 825552| ≤ 1 / (10^10) :=
  by 
    apply exp_approx_start 
    iterate 13 
      refine'
        exp_1_approx_succ_eq
          (by 
            normNum1 <;> rfl)
          (by 
            normCast <;> rfl)
          _ 
    normNum1 
    refine'
      exp_approx_end' _
        (by 
          normNum1 <;> rfl)
        _
        (by 
          normCast <;> rfl)
        (by 
          simp )
        _ 
    rw [_root_.abs_one, abs_of_pos] <;> normNum1

theorem exp_one_near_20 : |exp 1 - 363916618873 / 133877442384| ≤ 1 / (10^20) :=
  by 
    apply exp_approx_start 
    iterate 21 
      refine'
        exp_1_approx_succ_eq
          (by 
            normNum1 <;> rfl)
          (by 
            normCast <;> rfl)
          _ 
    normNum1 
    refine'
      exp_approx_end' _
        (by 
          normNum1 <;> rfl)
        _
        (by 
          normCast <;> rfl)
        (by 
          simp )
        _ 
    rw [_root_.abs_one, abs_of_pos] <;> normNum1

theorem exp_one_gt_d9 : 2.7182818283 < exp 1 :=
  lt_of_lt_of_leₓ
    (by 
      normNum)
    (sub_le.1 (abs_sub_le_iff.1 exp_one_near_10).2)

theorem exp_one_lt_d9 : exp 1 < 2.7182818286 :=
  lt_of_le_of_ltₓ (sub_le_iff_le_add.1 (abs_sub_le_iff.1 exp_one_near_10).1)
    (by 
      normNum)

theorem exp_neg_one_gt_d9 : 0.36787944116 < exp (-1) :=
  by 
    rw [exp_neg, lt_inv _ (exp_pos _)]
    refine' lt_of_le_of_ltₓ (sub_le_iff_le_add.1 (abs_sub_le_iff.1 exp_one_near_10).1) _ 
    all_goals 
      normNum

theorem exp_neg_one_lt_d9 : exp (-1) < 0.3678794412 :=
  by 
    rw [exp_neg, inv_lt (exp_pos _)]
    refine' lt_of_lt_of_leₓ _ (sub_le.1 (abs_sub_le_iff.1 exp_one_near_10).2)
    all_goals 
      normNum

-- error in Data.Complex.ExponentialBounds: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem log_two_near_10 : «expr ≤ »(«expr| |»(«expr - »(log 2, «expr / »(287209, 414355))), «expr / »(1, «expr ^ »(10, 10))) :=
begin
  suffices [] [":", expr «expr ≤ »(«expr| |»(«expr - »(log 2, «expr / »(287209, 414355))), «expr + »(«expr / »(1, 17179869184), «expr - »(«expr / »(1, «expr ^ »(10, 10)), «expr / »(1, «expr ^ »(2, 34)))))],
  { norm_num1 ["at", "*"],
    assumption },
  have [ident t] [":", expr «expr = »(«expr| |»((«expr ⁻¹»(2) : exprℝ())), «expr ⁻¹»(2))] [],
  { rw [expr abs_of_pos] [],
    norm_num [] [] },
  have [ident z] [] [":=", expr real.abs_log_sub_add_sum_range_le (show «expr < »(«expr| |»((«expr ⁻¹»(2) : exprℝ())), 1), by { rw [expr t] [],
      norm_num [] [] }) 34],
  rw [expr t] ["at", ident z],
  norm_num1 ["at", ident z],
  rw ["[", expr one_div (2 : exprℝ()), ",", expr log_inv, ",", "<-", expr sub_eq_add_neg, ",", expr _root_.abs_sub_comm, "]"] ["at", ident z],
  apply [expr le_trans (_root_.abs_sub_le _ _ _) (add_le_add z _)],
  simp_rw ["[", expr sum_range_succ, "]"] [],
  norm_num [] [],
  rw [expr abs_of_pos] []; norm_num [] []
end

theorem log_two_gt_d9 : 0.6931471803 < log 2 :=
  lt_of_lt_of_leₓ
    (by 
      normNum1)
    (sub_le.1 (abs_sub_le_iff.1 log_two_near_10).2)

theorem log_two_lt_d9 : log 2 < 0.6931471808 :=
  lt_of_le_of_ltₓ (sub_le_iff_le_add.1 (abs_sub_le_iff.1 log_two_near_10).1)
    (by 
      normNum)

end Real

