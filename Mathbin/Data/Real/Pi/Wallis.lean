import Mathbin.Analysis.SpecialFunctions.Integrals

/-! ### The Wallis Product for Pi -/


namespace Real

open_locale Real TopologicalSpace BigOperators

open Filter Finset intervalIntegral

-- error in Data.Real.Pi.Wallis: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem integral_sin_pow_div_tendsto_one : tendsto (λ
 k, «expr / »(«expr∫ in .. , »((x), 0, exprπ(), «expr ^ »(sin x, «expr + »(«expr * »(2, k), 1))), «expr∫ in .. , »((x), 0, exprπ(), «expr ^ »(sin x, «expr * »(2, k))))) at_top (expr𝓝() 1) :=
begin
  have [ident h₃] [":", expr ∀
   n, «expr ≤ »(«expr / »(«expr∫ in .. , »((x), 0, exprπ(), «expr ^ »(sin x, «expr + »(«expr * »(2, n), 1))), «expr∫ in .. , »((x), 0, exprπ(), «expr ^ »(sin x, «expr * »(2, n)))), 1)] [":=", expr λ
   n, (div_le_one (integral_sin_pow_pos _)).mpr (integral_sin_pow_succ_le _)],
  have [ident h₄] [":", expr ∀
   n, «expr ≥ »(«expr / »(«expr∫ in .. , »((x), 0, exprπ(), «expr ^ »(sin x, «expr + »(«expr * »(2, n), 1))), «expr∫ in .. , »((x), 0, exprπ(), «expr ^ »(sin x, «expr * »(2, n)))), «expr / »(«expr * »(2, n), «expr + »(«expr * »(2, n), 1)))] [],
  { rintro ["⟨", ident n, "⟩"],
    { have [] [":", expr «expr ≤ »(0, «expr / »(«expr + »(1, 1), exprπ()))] [],
      exact [expr div_nonneg (by norm_num [] []) pi_pos.le],
      simp [] [] [] ["[", expr this, "]"] [] [] },
    calc
      «expr ≥ »(«expr / »(«expr∫ in .. , »((x), 0, exprπ(), «expr ^ »(sin x, «expr + »(«expr * »(2, n.succ), 1))), «expr∫ in .. , »((x), 0, exprπ(), «expr ^ »(sin x, «expr * »(2, n.succ)))), «expr / »(«expr∫ in .. , »((x), 0, exprπ(), «expr ^ »(sin x, «expr + »(«expr * »(2, n.succ), 1))), «expr∫ in .. , »((x), 0, exprπ(), «expr ^ »(sin x, «expr + »(«expr * »(2, n), 1))))) : by { refine [expr div_le_div (integral_sin_pow_pos _).le (le_refl _) (integral_sin_pow_pos _) _],
        convert [] [expr integral_sin_pow_succ_le «expr + »(«expr * »(2, n), 1)] ["using", 1] }
      «expr = »(..., «expr / »(«expr * »(2, «expr↑ »(n.succ)), «expr + »(«expr * »(2, «expr↑ »(n.succ)), 1))) : by { rw [expr div_eq_iff (integral_sin_pow_pos «expr + »(«expr * »(2, n), 1)).ne'] [],
        convert [] [expr integral_sin_pow «expr + »(«expr * »(2, n), 1)] [],
        simp [] [] [] [] ["with", ident field_simps] [],
        norm_cast [] } },
  refine [expr tendsto_of_tendsto_of_tendsto_of_le_of_le _ _ (λ n, (h₄ n).le) (λ n, h₃ n)],
  { refine [expr metric.tendsto_at_top.mpr (λ ε hε, ⟨«expr⌈ ⌉₊»(«expr / »(1, ε)), λ n hn, _⟩)],
    have [ident h] [":", expr «expr = »(«expr - »(«expr / »(«expr * »((2 : exprℝ()), n), «expr + »(«expr * »(2, n), 1)), 1), «expr / »(«expr- »(1), «expr + »(«expr * »(2, n), 1)))] [],
    { conv_lhs [] [] { congr,
        skip,
        rw ["<-", expr @div_self _ _ «expr + »(«expr * »((2 : exprℝ()), n), 1) (by { norm_cast [],
            linarith [] [] [] })] },
      rw ["[", "<-", expr sub_div, ",", "<-", expr sub_sub, ",", expr sub_self, ",", expr zero_sub, "]"] [] },
    have [ident hpos] [":", expr «expr < »((0 : exprℝ()), «expr + »(«expr * »(2, n), 1))] [],
    { norm_cast [],
      norm_num [] [] },
    rw ["[", expr dist_eq, ",", expr h, ",", expr abs_div, ",", expr abs_neg, ",", expr abs_one, ",", expr abs_of_pos hpos, ",", expr one_div_lt hpos hε, "]"] [],
    calc
      «expr ≤ »(«expr / »(1, ε), «expr⌈ ⌉₊»(«expr / »(1, ε))) : nat.le_ceil _
      «expr ≤ »(..., n) : by exact_mod_cast [expr hn.le]
      «expr < »(..., «expr + »(«expr * »(2, n), 1)) : by { norm_cast [],
        linarith [] [] [] } },
  { exact [expr tendsto_const_nhds] }
end

-- error in Data.Real.Pi.Wallis: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- This theorem establishes the Wallis Product for `π`. Our proof is largely about analyzing
  the behavior of the ratio of the integral of `sin x ^ n` as `n → ∞`.
  See: https://en.wikipedia.org/wiki/Wallis_product

  The proof can be broken down into two pieces.
  (Pieces involving general properties of the integral of `sin x ^n` can be found
  in `analysis.special_functions.integrals`.) First, we use integration by parts to obtain a
  recursive formula for `∫ x in 0..π, sin x ^ (n + 2)` in terms of `∫ x in 0..π, sin x ^ n`.
  From this we can obtain closed form products of `∫ x in 0..π, sin x ^ (2 * n)` and
  `∫ x in 0..π, sin x ^ (2 * n + 1)` via induction. Next, we study the behavior of the ratio
  `∫ (x : ℝ) in 0..π, sin x ^ (2 * k + 1)) / ∫ (x : ℝ) in 0..π, sin x ^ (2 * k)` and prove that
  it converges to one using the squeeze theorem. The final product for `π` is obtained after some
  algebraic manipulation. -/
theorem tendsto_prod_pi_div_two : tendsto (λ
 k, «expr∏ in , »((i), range k, «expr * »(«expr / »(«expr + »(«expr * »((2 : exprℝ()), i), 2), «expr + »(«expr * »(2, i), 1)), «expr / »(«expr + »(«expr * »(2, i), 2), «expr + »(«expr * »(2, i), 3))))) at_top (expr𝓝() «expr / »(exprπ(), 2)) :=
begin
  suffices [ident h] [":", expr tendsto (λ
    k, «expr * »(«expr / »(2, exprπ()), «expr∏ in , »((i), range k, «expr * »(«expr / »(«expr + »(«expr * »((2 : exprℝ()), i), 2), «expr + »(«expr * »(2, i), 1)), «expr / »(«expr + »(«expr * »(2, i), 2), «expr + »(«expr * »(2, i), 3)))))) at_top (expr𝓝() 1)],
  { have [] [] [":=", expr tendsto.const_mul «expr / »(exprπ(), 2) h],
    have [ident h] [":", expr «expr ≠ »(«expr / »(exprπ(), 2), 0)] [],
    norm_num ["[", expr pi_ne_zero, "]"] [],
    simp [] [] ["only"] ["[", "<-", expr mul_assoc, ",", "<-", expr @inv_div _ _ exprπ() 2, ",", expr mul_inv_cancel h, ",", expr one_mul, ",", expr mul_one, "]"] [] ["at", ident this],
    exact [expr this] },
  have [ident h] [":", expr «expr = »(λ
    k : exprℕ(), «expr * »(«expr / »((2 : exprℝ()), exprπ()), «expr∏ in , »((i : exprℕ()), range k, «expr * »(«expr / »(«expr + »(«expr * »(2, i), 2), «expr + »(«expr * »(2, i), 1)), «expr / »(«expr + »(«expr * »(2, i), 2), «expr + »(«expr * »(2, i), 3))))), λ
    k, «expr / »(«expr * »(2, «expr∏ in , »((i), range k, «expr / »(«expr + »(«expr * »(2, i), 2), «expr + »(«expr * »(2, i), 3)))), «expr * »(exprπ(), «expr∏ in , »((i : exprℕ()), range k, «expr / »(«expr + »(«expr * »(2, i), 1), «expr + »(«expr * »(2, i), 2))))))] [],
  { funext [],
    have [ident h] [":", expr «expr = »(«expr∏ in , »((i : exprℕ()), range k, «expr / »(«expr + »(«expr * »((2 : exprℝ()), «expr↑ »(i)), 2), «expr + »(«expr * »(2, «expr↑ »(i)), 1))), «expr / »(1, «expr∏ in , »((i : exprℕ()), range k, «expr / »(«expr + »(«expr * »(2, «expr↑ »(i)), 1), «expr + »(«expr * »(2, «expr↑ »(i)), 2)))))] [],
    { rw ["[", expr one_div, ",", "<-", expr finset.prod_inv_distrib', "]"] [],
      refine [expr prod_congr rfl (λ x hx, _)],
      field_simp [] [] [] [] },
    rw ["[", expr prod_mul_distrib, ",", expr h, "]"] [],
    field_simp [] [] [] [] },
  simp [] [] ["only"] ["[", expr h, ",", "<-", expr integral_sin_pow_even, ",", "<-", expr integral_sin_pow_odd, "]"] [] [],
  exact [expr integral_sin_pow_div_tendsto_one]
end

end Real

