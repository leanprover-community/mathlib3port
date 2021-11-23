import Mathbin.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Pi

This file contains lemmas which establish bounds on `real.pi`.
Notably, these include `pi_gt_sqrt_two_add_series` and `pi_lt_sqrt_two_add_series`,
which bound `π` using series;
numerical bounds on `π` such as `pi_gt_314`and `pi_lt_315` (more precise versions are given, too).

See also `data.real.pi.leibniz` and `data.real.pi.wallis` for infinite formulas for `π`.
-/


open_locale Real

namespace Real

-- error in Data.Real.Pi.Bounds: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem pi_gt_sqrt_two_add_series
(n : exprℕ()) : «expr < »(«expr * »(«expr ^ »(2, «expr + »(n, 1)), sqrt «expr - »(2, sqrt_two_add_series 0 n)), exprπ()) :=
begin
  have [] [":", expr «expr < »(«expr * »(«expr / »(sqrt «expr - »(2, sqrt_two_add_series 0 n), 2), «expr ^ »(2, «expr + »(n, 2))), exprπ())] [],
  { rw ["[", "<-", expr lt_div_iff, ",", "<-", expr sin_pi_over_two_pow_succ, "]"] [],
    apply [expr sin_lt],
    apply [expr div_pos pi_pos],
    all_goals { apply [expr pow_pos],
      norm_num [] [] } },
  apply [expr lt_of_le_of_lt (le_of_eq _) this],
  rw ["[", expr pow_succ _ «expr + »(n, 1), ",", "<-", expr mul_assoc, ",", expr div_mul_cancel, ",", expr mul_comm, "]"] [],
  norm_num [] []
end

-- error in Data.Real.Pi.Bounds: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem pi_lt_sqrt_two_add_series
(n : exprℕ()) : «expr < »(exprπ(), «expr + »(«expr * »(«expr ^ »(2, «expr + »(n, 1)), sqrt «expr - »(2, sqrt_two_add_series 0 n)), «expr / »(1, «expr ^ »(4, n)))) :=
begin
  have [] [":", expr «expr < »(exprπ(), «expr * »(«expr + »(«expr / »(sqrt «expr - »(2, sqrt_two_add_series 0 n), 2), «expr / »(«expr / »(1, «expr ^ »(«expr ^ »(2, n), 3)), 4)), «expr ^ »(2, «expr + »(n, 2))))] [],
  { rw ["[", "<-", expr div_lt_iff, ",", "<-", expr sin_pi_over_two_pow_succ, "]"] [],
    refine [expr lt_of_lt_of_le (lt_add_of_sub_right_lt (sin_gt_sub_cube _ _)) _],
    { apply [expr div_pos pi_pos],
      apply [expr pow_pos],
      norm_num [] [] },
    { rw [expr div_le_iff'] [],
      { refine [expr le_trans pi_le_four _],
        simp [] [] ["only"] ["[", expr show «expr = »((4 : exprℝ()), «expr ^ »(2, 2)), by norm_num [] [], ",", expr mul_one, "]"] [] [],
        apply [expr pow_le_pow],
        norm_num [] [],
        apply [expr le_add_of_nonneg_left],
        apply [expr nat.zero_le] },
      { apply [expr pow_pos],
        norm_num [] [] } },
    apply [expr add_le_add_left],
    rw [expr div_le_div_right] [],
    rw ["[", expr le_div_iff, ",", "<-", expr mul_pow, "]"] [],
    refine [expr le_trans _ (le_of_eq (one_pow 3))],
    apply [expr pow_le_pow_of_le_left],
    { apply [expr le_of_lt],
      apply [expr mul_pos],
      apply [expr div_pos pi_pos],
      apply [expr pow_pos],
      norm_num [] [],
      apply [expr pow_pos],
      norm_num [] [] },
    rw ["<-", expr le_div_iff] [],
    refine [expr le_trans ((div_le_div_right _).mpr pi_le_four) _],
    apply [expr pow_pos],
    norm_num [] [],
    rw ["[", expr pow_succ, ",", expr pow_succ, ",", "<-", expr mul_assoc, ",", "<-", expr div_div_eq_div_mul, "]"] [],
    convert [] [expr le_refl _] [],
    all_goals { repeat { apply [expr pow_pos] },
      norm_num [] [] } },
  apply [expr lt_of_lt_of_le this (le_of_eq _)],
  rw ["[", expr add_mul, "]"] [],
  congr' [1] [],
  { rw ["[", expr pow_succ _ «expr + »(n, 1), ",", "<-", expr mul_assoc, ",", expr div_mul_cancel, ",", expr mul_comm, "]"] [],
    norm_num [] [] },
  rw ["[", expr pow_succ, ",", "<-", expr pow_mul, ",", expr mul_comm n 2, ",", expr pow_mul, ",", expr show «expr = »(«expr ^ »((2 : exprℝ()), 2), 4), by norm_num [] [], ",", expr pow_succ, ",", expr pow_succ, ",", "<-", expr mul_assoc (2 : exprℝ()), ",", expr show «expr = »(«expr * »((2 : exprℝ()), 2), 4), by norm_num [] [], ",", "<-", expr mul_assoc, ",", expr div_mul_cancel, ",", expr mul_comm «expr ^ »((2 : exprℝ()), n), ",", "<-", expr div_div_eq_div_mul, ",", expr div_mul_cancel, "]"] [],
  apply [expr pow_ne_zero],
  norm_num [] [],
  norm_num [] []
end

/-- From an upper bound on `sqrt_two_add_series 0 n = 2 cos (π / 2 ^ (n+1))` of the form
`sqrt_two_add_series 0 n ≤ 2 - (a / 2 ^ (n + 1)) ^ 2)`, one can deduce the lower bound `a < π`
thanks to basic trigonometric inequalities as expressed in `pi_gt_sqrt_two_add_series`. -/
theorem pi_lower_bound_start (n : ℕ) {a} (h : sqrt_two_add_series ((0 : ℕ) / (1 : ℕ)) n ≤ 2 - (a / (2^n+1)^2)) :
  a < π :=
  by 
    refine' lt_of_le_of_ltₓ _ (pi_gt_sqrt_two_add_series n)
    rw [mul_commₓ]
    refine'
      (div_le_iff
            (pow_pos
              (by 
                normNum)
              _ :
            (0 : ℝ) < _)).mp
        (le_sqrt_of_sq_le _)
    rwa [le_sub,
      show (0 : ℝ) = (0 : ℕ) / (1 : ℕ)by 
        rw [Nat.cast_zero, zero_div]]

-- error in Data.Real.Pi.Bounds: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem sqrt_two_add_series_step_up
(c d : exprℕ())
{a b n : exprℕ()}
{z : exprℝ()}
(hz : «expr ≤ »(sqrt_two_add_series «expr / »(c, d) n, z))
(hb : «expr < »(0, b))
(hd : «expr < »(0, d))
(h : «expr ≤ »(«expr * »(«expr + »(«expr * »(2, b), a), «expr ^ »(d, 2)), «expr * »(«expr ^ »(c, 2), b))) : «expr ≤ »(sqrt_two_add_series «expr / »(a, b) «expr + »(n, 1), z) :=
begin
  refine [expr le_trans _ hz],
  rw [expr sqrt_two_add_series_succ] [],
  apply [expr sqrt_two_add_series_monotone_left],
  have [ident hb'] [":", expr «expr < »(0, (b : exprℝ()))] [":=", expr nat.cast_pos.2 hb],
  have [ident hd'] [":", expr «expr < »(0, (d : exprℝ()))] [":=", expr nat.cast_pos.2 hd],
  rw ["[", expr sqrt_le_left (div_nonneg c.cast_nonneg d.cast_nonneg), ",", expr div_pow, ",", expr add_div_eq_mul_add_div _ _ (ne_of_gt hb'), ",", expr div_le_div_iff hb' (pow_pos hd' _), "]"] [],
  exact_mod_cast [expr h]
end

/-- Create a proof of `a < π` for a fixed rational number `a`, given a witness, which is a
sequence of rational numbers `sqrt 2 < r 1 < r 2 < ... < r n < 2` satisfying the property that
`sqrt (2 + r i) ≤ r(i+1)`, where `r 0 = 0` and `sqrt (2 - r n) ≥ a/2^(n+1)`. -/
unsafe def pi_lower_bound (l : List ℚ) : tactic Unit :=
  do 
    let n := l.length 
    tactic.apply (quote.1 (@pi_lower_bound_start (%%ₓreflect n)))
    l.mmap'
        fun r =>
          do 
            let a := r.num.to_nat 
            let b := r.denom
            () <$ tactic.apply (quote.1 (@sqrt_two_add_series_step_up (%%ₓreflect a) (%%ₓreflect b)));
                [tactic.skip, sorry, sorry, sorry]
    sorry 
    sorry

/-- From a lower bound on `sqrt_two_add_series 0 n = 2 cos (π / 2 ^ (n+1))` of the form
`2 - ((a - 1 / 4 ^ n) / 2 ^ (n + 1)) ^ 2 ≤ sqrt_two_add_series 0 n`, one can deduce the upper bound
`π < a` thanks to basic trigonometric formulas as expressed in `pi_lt_sqrt_two_add_series`. -/
theorem pi_upper_bound_start (n : ℕ) {a}
  (h : 2 - ((a - 1 / (4^n)) / (2^n+1)^2) ≤ sqrt_two_add_series ((0 : ℕ) / (1 : ℕ)) n) (h₂ : 1 / (4^n) ≤ a) : π < a :=
  by 
    refine' lt_of_lt_of_leₓ (pi_lt_sqrt_two_add_series n) _ 
    rw [←le_sub_iff_add_le, ←le_div_iff', sqrt_le_left, sub_le]
    ·
      rwa [Nat.cast_zero, zero_div] at h
    ·
      exact div_nonneg (sub_nonneg.2 h₂) (pow_nonneg (le_of_ltₓ zero_lt_two) _)
    ·
      exact pow_pos zero_lt_two _

-- error in Data.Real.Pi.Bounds: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem sqrt_two_add_series_step_down
(a b : exprℕ())
{c d n : exprℕ()}
{z : exprℝ()}
(hz : «expr ≤ »(z, sqrt_two_add_series «expr / »(a, b) n))
(hb : «expr < »(0, b))
(hd : «expr < »(0, d))
(h : «expr ≤ »(«expr * »(«expr ^ »(a, 2), d), «expr * »(«expr + »(«expr * »(2, d), c), «expr ^ »(b, 2)))) : «expr ≤ »(z, sqrt_two_add_series «expr / »(c, d) «expr + »(n, 1)) :=
begin
  apply [expr le_trans hz],
  rw [expr sqrt_two_add_series_succ] [],
  apply [expr sqrt_two_add_series_monotone_left],
  apply [expr le_sqrt_of_sq_le],
  have [ident hb'] [":", expr «expr < »(0, (b : exprℝ()))] [":=", expr nat.cast_pos.2 hb],
  have [ident hd'] [":", expr «expr < »(0, (d : exprℝ()))] [":=", expr nat.cast_pos.2 hd],
  rw ["[", expr div_pow, ",", expr add_div_eq_mul_add_div _ _ (ne_of_gt hd'), ",", expr div_le_div_iff (pow_pos hb' _) hd', "]"] [],
  exact_mod_cast [expr h]
end

/-- Create a proof of `π < a` for a fixed rational number `a`, given a witness, which is a
sequence of rational numbers `sqrt 2 < r 1 < r 2 < ... < r n < 2` satisfying the property that
`sqrt (2 + r i) ≥ r(i+1)`, where `r 0 = 0` and `sqrt (2 - r n) ≥ (a - 1/4^n) / 2^(n+1)`. -/
unsafe def pi_upper_bound (l : List ℚ) : tactic Unit :=
  do 
    let n := l.length
    () <$ tactic.apply (quote.1 (@pi_upper_bound_start (%%ₓreflect n))); [pure (), sorry]
    l.mmap'
        fun r =>
          do 
            let a := r.num.to_nat 
            let b := r.denom
            () <$ tactic.apply (quote.1 (@sqrt_two_add_series_step_down (%%ₓreflect a) (%%ₓreflect b)));
                [pure (), sorry, sorry, sorry]
    sorry 
    sorry

theorem pi_gt_three : 3 < π :=
  by 
    runTac 
      pi_lower_bound [23 / 16]

theorem pi_gt_314 : 3.14 < π :=
  by 
    runTac 
      pi_lower_bound [99 / 70, 874 / 473, 1940 / 989, 1447 / 727]

theorem pi_lt_315 : π < 3.15 :=
  by 
    runTac 
      pi_upper_bound [140 / 99, 279 / 151, 51 / 26, 412 / 207]

theorem pi_gt_31415 : 3.1415 < π :=
  by 
    runTac 
      pi_lower_bound [11482 / 8119, 5401 / 2923, 2348 / 1197, 11367 / 5711, 25705 / 12868, 23235 / 11621]

theorem pi_lt_31416 : π < 3.1416 :=
  by 
    runTac 
      pi_upper_bound
          [4756 / 3363, 101211 / 54775, 505534 / 257719, 83289 / 41846, 411278 / 205887, 438142 / 219137,
            451504 / 225769, 265603 / 132804, 849938 / 424971]

theorem pi_gt_3141592 : 3.141592 < π :=
  by 
    runTac 
      pi_lower_bound
          [11482 / 8119, 7792 / 4217, 54055 / 27557, 949247 / 476920, 3310126 / 1657059, 2635492 / 1318143,
            1580265 / 790192, 1221775 / 610899, 3612247 / 1806132, 849943 / 424972]

theorem pi_lt_3141593 : π < 3.141593 :=
  by 
    runTac 
      pi_upper_bound
          [27720 / 19601, 56935 / 30813, 49359 / 25163, 258754 / 130003, 113599 / 56868, 1101994 / 551163,
            8671537 / 4336095, 3877807 / 1938940, 52483813 / 26242030, 56946167 / 28473117, 23798415 / 11899211]

end Real

