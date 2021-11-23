import Mathbin.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv

/-! ### Leibniz's Series for Pi -/


namespace Real

open Filter Set

open_locale Classical BigOperators TopologicalSpace Real

local notation "|" x "|" => abs x

-- error in Data.Real.Pi.Leibniz: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- This theorem establishes **Leibniz's series for `π`**: The alternating sum of the reciprocals
  of the odd numbers is `π/4`. Note that this is a conditionally rather than absolutely convergent
  series. The main tool that this proof uses is the Mean Value Theorem (specifically avoiding the
  Fundamental Theorem of Calculus).

  Intuitively, the theorem holds because Leibniz's series is the Taylor series of `arctan x`
  centered about `0` and evaluated at the value `x = 1`. Therefore, much of this proof consists of
  reasoning about a function
    `f := arctan x - ∑ i in finset.range k, (-(1:ℝ))^i * x^(2*i+1) / (2*i+1)`,
  the difference between `arctan` and the `k`-th partial sum of its Taylor series. Some ingenuity is
  required due to the fact that the Taylor series is not absolutely convergent at `x = 1`.

  This proof requires a bound on `f 1`, the key idea being that `f 1` can be split as the sum of
  `f 1 - f u` and `f u`, where `u` is a sequence of values in [0,1], carefully chosen such that
  each of these two terms can be controlled (in different ways).

  We begin the proof by (1) introducing that sequence `u` and then proving that another sequence
  constructed from `u` tends to `0` at `+∞`. After (2) converting the limit in our goal to an
  inequality, we (3) introduce the auxiliary function `f` defined above. Next, we (4) compute the
  derivative of `f`, denoted by `f'`, first generally and then on each of two subintervals of [0,1].
  We then (5) prove a bound for `f'`, again both generally as well as on each of the two
  subintervals. Finally, we (6) apply the Mean Value Theorem twice, obtaining bounds on `f 1 - f u`
  and `f u - f 0` from the bounds on `f'` (note that `f 0 = 0`). -/
theorem tendsto_sum_pi_div_four : tendsto (λ
 k, «expr∑ in , »((i), finset.range k, «expr / »(«expr ^ »(«expr- »((1 : exprℝ())), i), «expr + »(«expr * »(2, i), 1)))) at_top (expr𝓝() «expr / »(exprπ(), 4)) :=
begin
  rw ["[", expr tendsto_iff_norm_tendsto_zero, ",", "<-", expr tendsto_zero_iff_norm_tendsto_zero, "]"] [],
  let [ident u] [] [":=", expr λ
   k : exprℕ(), «expr ^ »((k : nnreal), «expr / »(«expr- »(1), «expr + »(«expr * »(2, (k : exprℝ())), 1)))],
  have [ident H] [":", expr tendsto (λ
    k : exprℕ(), «expr + »(«expr - »((1 : exprℝ()), u k), «expr ^ »(u k, «expr + »(«expr * »(2, (k : exprℝ())), 1)))) at_top (expr𝓝() 0)] [],
  { convert [] [expr (((tendsto_rpow_div_mul_add «expr- »(1) 2 1 two_ne_zero.symm).neg.const_add 1).add tendsto_inv_at_top_zero).comp tendsto_coe_nat_at_top_at_top] [],
    { ext [] [ident k] [],
      simp [] [] ["only"] ["[", expr nnreal.coe_nat_cast, ",", expr function.comp_app, ",", expr nnreal.coe_rpow, "]"] [] [],
      rw ["[", "<-", expr rpow_mul (nat.cast_nonneg k) «expr / »(«expr- »(1), «expr + »(«expr * »(2, (k : exprℝ())), 1)) «expr + »(«expr * »(2, (k : exprℝ())), 1), ",", expr @div_mul_cancel _ _ _ «expr + »(«expr * »(2, (k : exprℝ())), 1) (by { norm_cast [],
          simp [] [] ["only"] ["[", expr nat.succ_ne_zero, ",", expr not_false_iff, "]"] [] [] }), ",", expr rpow_neg_one k, ",", expr sub_eq_add_neg, "]"] [] },
    { simp [] [] ["only"] ["[", expr add_zero, ",", expr add_right_neg, "]"] [] [] } },
  refine [expr squeeze_zero_norm _ H],
  intro [ident k],
  let [ident U] [] [":=", expr u k],
  let [ident b] [] [":=", expr λ
   (i : exprℕ())
   (x), «expr / »(«expr * »(«expr ^ »(«expr- »((1 : exprℝ())), i), «expr ^ »(x, «expr + »(«expr * »(2, i), 1))), «expr + »(«expr * »(2, i), 1))],
  let [ident f] [] [":=", expr λ x, «expr - »(arctan x, «expr∑ in , »((i), finset.range k, b i x))],
  suffices [ident f_bound] [":", expr «expr ≤ »(«expr| |»(«expr - »(f 1, f 0)), «expr + »(«expr - »((1 : exprℝ()), U), «expr ^ »(U, «expr + »(«expr * »(2, (k : exprℝ())), 1))))],
  { rw ["<-", expr norm_neg] [],
    convert [] [expr f_bound] [],
    simp [] [] ["only"] ["[", expr f, "]"] [] [],
    simp [] [] [] ["[", expr b, "]"] [] [] },
  have [ident hU1] [":", expr «expr ≤ »((U : exprℝ()), 1)] [],
  { by_cases [expr hk, ":", expr «expr = »(k, 0)],
    { simpa [] [] ["only"] ["[", expr U, ",", expr hk, "]"] [] ["using", expr zero_rpow_le_one _] },
    { exact [expr rpow_le_one_of_one_le_of_nonpos (by { norm_cast [],
          exact [expr nat.succ_le_iff.mpr (nat.pos_of_ne_zero hk)] }) (le_of_lt (@div_neg_of_neg_of_pos _ _ «expr- »((1 : exprℝ())) «expr + »(«expr * »(2, k), 1) (neg_neg_iff_pos.mpr zero_lt_one) (by { norm_cast [],
            exact [expr nat.succ_pos'] })))] } },
  have [ident hU2] [] [":=", expr nnreal.coe_nonneg U],
  let [ident f'] [] [":=", expr λ
   x : exprℝ(), «expr / »(«expr ^ »(«expr- »(«expr ^ »(x, 2)), k), «expr + »(1, «expr ^ »(x, 2)))],
  have [ident has_deriv_at_f] [":", expr ∀ x, has_deriv_at f (f' x) x] [],
  { intro [ident x],
    have [ident has_deriv_at_b] [":", expr ∀
     i «expr ∈ » finset.range k, has_deriv_at (b i) «expr ^ »(«expr- »(«expr ^ »(x, 2)), i) x] [],
    { intros [ident i, ident hi],
      convert [] [expr has_deriv_at.const_mul «expr / »(«expr ^ »((«expr- »(1) : exprℝ()), i), «expr + »(«expr * »(2, i), 1)) (@has_deriv_at.pow _ _ _ _ _ «expr + »(«expr * »(2, i), 1) (has_deriv_at_id x))] [],
      { ext [] [ident y] [],
        simp [] [] ["only"] ["[", expr b, ",", expr id.def, "]"] [] [],
        ring [] },
      { simp [] [] ["only"] ["[", expr nat.add_succ_sub_one, ",", expr add_zero, ",", expr mul_one, ",", expr id.def, ",", expr nat.cast_bit0, ",", expr nat.cast_add, ",", expr nat.cast_one, ",", expr nat.cast_mul, "]"] [] [],
        rw ["[", "<-", expr mul_assoc, ",", expr @div_mul_cancel _ _ _ «expr + »(«expr * »(2, (i : exprℝ())), 1) (by { norm_cast [],
            linarith [] [] [] }), ",", expr pow_mul x 2 i, ",", "<-", expr mul_pow «expr- »(1) «expr ^ »(x, 2) i, "]"] [],
        ring_nf [] [] [] } },
    convert [] [expr (has_deriv_at_arctan x).sub (has_deriv_at.sum has_deriv_at_b)] [],
    have [ident g_sum] [] [":=", expr @geom_sum_eq _ _ «expr- »(«expr ^ »(x, 2)) ((neg_nonpos.mpr (sq_nonneg x)).trans_lt zero_lt_one).ne k],
    simp [] [] ["only"] ["[", expr geom_sum, ",", expr f', "]"] [] ["at", ident g_sum, "⊢"],
    rw ["[", expr g_sum, ",", "<-", expr neg_add' «expr ^ »(x, 2) 1, ",", expr add_comm «expr ^ »(x, 2) 1, ",", expr sub_eq_add_neg, ",", expr neg_div', ",", expr neg_div_neg_eq, "]"] [],
    ring [] },
  have [ident hderiv1] [":", expr ∀
   x «expr ∈ » Icc (U : exprℝ()) 1, has_deriv_within_at f (f' x) (Icc (U : exprℝ()) 1) x] [":=", expr λ
   x hx, (has_deriv_at_f x).has_deriv_within_at],
  have [ident hderiv2] [":", expr ∀
   x «expr ∈ » Icc 0 (U : exprℝ()), has_deriv_within_at f (f' x) (Icc 0 (U : exprℝ())) x] [":=", expr λ
   x hx, (has_deriv_at_f x).has_deriv_within_at],
  have [ident f'_bound] [":", expr ∀
   x «expr ∈ » Icc («expr- »(1) : exprℝ()) 1, «expr ≤ »(«expr| |»(f' x), «expr ^ »(«expr| |»(x), «expr * »(2, k)))] [],
  { intros [ident x, ident hx],
    rw ["[", expr abs_div, ",", expr is_absolute_value.abv_pow abs «expr- »(«expr ^ »(x, 2)) k, ",", expr abs_neg, ",", expr is_absolute_value.abv_pow abs x 2, ",", expr tactic.ring_exp.pow_e_pf_exp rfl rfl, "]"] [],
    refine [expr div_le_of_nonneg_of_le_mul (abs_nonneg _) (pow_nonneg (abs_nonneg _) _) _],
    refine [expr le_mul_of_one_le_right (pow_nonneg (abs_nonneg _) _) _],
    rw [expr abs_of_nonneg (add_nonneg zero_le_one (sq_nonneg x) : «expr ≤ »((0 : exprℝ()), _))] [],
    exact [expr (le_add_of_nonneg_right (sq_nonneg x) : «expr ≤ »((1 : exprℝ()), _))] },
  have [ident hbound1] [":", expr ∀ x «expr ∈ » Ico (U : exprℝ()) 1, «expr ≤ »(«expr| |»(f' x), 1)] [],
  { rintros [ident x, "⟨", ident hx_left, ",", ident hx_right, "⟩"],
    have [ident hincr] [] [":=", expr pow_le_pow_of_le_left (le_trans hU2 hx_left) (le_of_lt hx_right) «expr * »(2, k)],
    rw ["[", expr one_pow «expr * »(2, k), ",", "<-", expr abs_of_nonneg (le_trans hU2 hx_left), "]"] ["at", ident hincr],
    rw ["<-", expr abs_of_nonneg (le_trans hU2 hx_left)] ["at", ident hx_right],
    linarith [] [] ["[", expr f'_bound x (mem_Icc.mpr (abs_le.mp (le_of_lt hx_right))), "]"] },
  have [ident hbound2] [":", expr ∀
   x «expr ∈ » Ico 0 (U : exprℝ()), «expr ≤ »(«expr| |»(f' x), «expr ^ »(U, «expr * »(2, k)))] [],
  { rintros [ident x, "⟨", ident hx_left, ",", ident hx_right, "⟩"],
    have [ident hincr] [] [":=", expr pow_le_pow_of_le_left hx_left (le_of_lt hx_right) «expr * »(2, k)],
    rw ["<-", expr abs_of_nonneg hx_left] ["at", ident hincr, ident hx_right],
    rw ["<-", expr abs_of_nonneg hU2] ["at", ident hU1, ident hx_right],
    linarith [] [] ["[", expr f'_bound x (mem_Icc.mpr (abs_le.mp (le_trans (le_of_lt hx_right) hU1))), "]"] },
  have [ident mvt1] [] [":=", expr norm_image_sub_le_of_norm_deriv_le_segment' hderiv1 hbound1 _ (right_mem_Icc.mpr hU1)],
  have [ident mvt2] [] [":=", expr norm_image_sub_le_of_norm_deriv_le_segment' hderiv2 hbound2 _ (right_mem_Icc.mpr hU2)],
  calc
    «expr = »(«expr| |»(«expr - »(f 1, f 0)), «expr| |»(«expr + »(«expr - »(f 1, f U), «expr - »(f U, f 0)))) : by ring_nf [] [] []
    «expr ≤ »(..., «expr + »(«expr * »(1, «expr - »(1, U)), «expr * »(«expr ^ »(U, «expr * »(2, k)), «expr - »(U, 0)))) : le_trans (abs_add «expr - »(f 1, f U) «expr - »(f U, f 0)) (add_le_add mvt1 mvt2)
    «expr = »(..., «expr + »(«expr - »(1, U), «expr * »(«expr ^ »(U, «expr * »(2, k)), U))) : by ring []
    «expr = »(..., «expr + »(«expr - »(1, u k), «expr ^ »(u k, «expr + »(«expr * »(2, (k : exprℝ())), 1)))) : by { rw ["[", "<-", expr pow_succ' (U : exprℝ()) «expr * »(2, k), "]"] [],
      norm_cast [] }
end

end Real

