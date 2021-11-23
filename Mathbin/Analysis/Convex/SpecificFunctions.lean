import Mathbin.Analysis.Calculus.MeanValue 
import Mathbin.Analysis.SpecialFunctions.PowDeriv

/-!
# Collection of convex functions

In this file we prove that the following functions are convex:

* `strict_convex_on_exp` : The exponential function is strictly convex.
* `even.convex_on_pow`, `even.strict_convex_on_pow` : For an even `n : ℕ`, `λ x, x ^ n` is convex
  and strictly convex when `2 ≤ n`.
* `convex_on_pow`, `strict_convex_on_pow` : For `n : ℕ`, `λ x, x ^ n` is convex on $[0, +∞)$ and
  strictly convex when `2 ≤ n`.
* `convex_on_zpow`, `strict_convex_on_zpow` : For `m : ℤ`, `λ x, x ^ m` is convex on $[0, +∞)$ and
  strictly convex when `m ≠ 0, 1`.
* `convex_on_rpow`, `strict_convex_on_rpow` : For `p : ℝ`, `λ x, x ^ p` is convex on $[0, +∞)$ when
  `1 ≤ p` and strictly convex when `1 < p`.
* `strict_concave_on_log_Ioi`, `strict_concave_on_log_Iio`: `real.log` is strictly concave on
  $(0, +∞)$ and $(-∞, 0)$ respectively.

## TODO

For `p : ℝ`, prove that `λ x, x ^ p` is concave when `0 ≤ p ≤ 1` and strictly concave when
`0 < p < 1`.
-/


open Real Set

open_locale BigOperators

/-- The norm of a real normed space is convex. Also see `seminorm.convex_on`. -/
theorem convex_on_norm {E : Type _} [NormedGroup E] [NormedSpace ℝ E] : ConvexOn ℝ univ (norm : E → ℝ) :=
  ⟨convex_univ,
    fun x y hx hy a b ha hb hab =>
      calc ∥(a • x)+b • y∥ ≤ ∥a • x∥+∥b • y∥ := norm_add_le _ _ 
        _ = (a*∥x∥)+b*∥y∥ :=
        by 
          rw [norm_smul, norm_smul, Real.norm_of_nonneg ha, Real.norm_of_nonneg hb]
        ⟩

/-- `exp` is strictly convex on the whole real line. -/
theorem strict_convex_on_exp : StrictConvexOn ℝ univ exp :=
  strict_convex_on_univ_of_deriv2_pos differentiable_exp fun x => (iter_deriv_exp 2).symm ▸ exp_pos x

/-- `exp` is convex on the whole real line. -/
theorem convex_on_exp : ConvexOn ℝ univ exp :=
  strict_convex_on_exp.ConvexOn

/-- `x^n`, `n : ℕ` is convex on the whole real line whenever `n` is even -/
theorem Even.convex_on_pow {n : ℕ} (hn : Even n) : ConvexOn ℝ Set.Univ fun x : ℝ => x^n :=
  by 
    apply convex_on_univ_of_deriv2_nonneg differentiable_pow
    ·
      simp only [deriv_pow', Differentiable.mul, differentiable_const, differentiable_pow]
    ·
      intro x 
      rcases Nat.Even.sub_even hn (Nat.even_bit0 1) with ⟨k, hk⟩
      rw [iter_deriv_pow, Finset.prod_range_cast_nat_sub, hk, pow_mul']
      exact mul_nonneg (Nat.cast_nonneg _) (pow_two_nonneg _)

/-- `x^n`, `n : ℕ` is strictly convex on the whole real line whenever `n ≠ 0` is even. -/
theorem Even.strict_convex_on_pow {n : ℕ} (hn : Even n) (h : n ≠ 0) : StrictConvexOn ℝ Set.Univ fun x : ℝ => x^n :=
  by 
    apply StrictMono.strict_convex_on_univ_of_deriv differentiable_pow 
    rw [deriv_pow']
    replace h := Nat.pos_of_ne_zeroₓ h 
    exact StrictMono.const_mul (Odd.strict_mono_pow$ Nat.Even.sub_odd h hn$ Nat.odd_iff.2 rfl) (Nat.cast_pos.2 h)

/-- `x^n`, `n : ℕ` is convex on `[0, +∞)` for all `n` -/
theorem convex_on_pow (n : ℕ) : ConvexOn ℝ (Ici 0) fun x : ℝ => x^n :=
  by 
    apply convex_on_of_deriv2_nonneg (convex_Ici _) (continuous_pow n).ContinuousOn differentiable_on_pow
    ·
      simp only [deriv_pow']
      exact (@differentiable_on_pow ℝ _ _ _).const_mul (n : ℝ)
    ·
      intro x hx 
      rw [iter_deriv_pow, Finset.prod_range_cast_nat_sub]
      exact mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (interior_subset hx) _)

/-- `x^n`, `n : ℕ` is strictly convex on `[0, +∞)` for all `n` greater than `2`. -/
theorem strict_convex_on_pow {n : ℕ} (hn : 2 ≤ n) : StrictConvexOn ℝ (Ici 0) fun x : ℝ => x^n :=
  by 
    apply StrictMonoOn.strict_convex_on_of_deriv (convex_Ici _) (continuous_on_pow _) differentiable_on_pow 
    rw [deriv_pow', interior_Ici]
    exact
      fun x hx : 0 < x y hy hxy =>
        mul_lt_mul_of_pos_left (pow_lt_pow_of_lt_left hxy hx.le$ Nat.sub_pos_of_ltₓ hn)
          (Nat.cast_pos.2$ zero_lt_two.trans_le hn)

theorem Finset.prod_nonneg_of_card_nonpos_even {α β : Type _} [LinearOrderedCommRing β] {f : α → β}
  [DecidablePred fun x => f x ≤ 0] {s : Finset α} (h0 : Even (s.filter fun x => f x ≤ 0).card) : 0 ≤ ∏x in s, f x :=
  calc 0 ≤ ∏x in s, (if f x ≤ 0 then (-1 : β) else 1)*f x :=
    Finset.prod_nonneg
      fun x _ =>
        by 
          splitIfs with hx hx
          ·
            simp [hx]
          simp  at hx⊢
          exact le_of_ltₓ hx 
    _ = _ :=
    by 
      rw [Finset.prod_mul_distrib, Finset.prod_ite, Finset.prod_const_one, mul_oneₓ, Finset.prod_const,
        neg_one_pow_eq_pow_mod_two, Nat.even_iff.1 h0, pow_zeroₓ, one_mulₓ]
    

-- error in Analysis.Convex.SpecificFunctions: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem int_prod_range_nonneg
(m : exprℤ())
(n : exprℕ())
(hn : even n) : «expr ≤ »(0, «expr∏ in , »((k), finset.range n, «expr - »(m, k))) :=
begin
  rcases [expr hn, "with", "⟨", ident n, ",", ident rfl, "⟩"],
  induction [expr n] [] ["with", ident n, ident ihn] [],
  { simp [] [] [] [] [] [] },
  rw ["[", expr nat.succ_eq_add_one, ",", expr mul_add, ",", expr mul_one, ",", expr bit0, ",", "<-", expr add_assoc, ",", expr finset.prod_range_succ, ",", expr finset.prod_range_succ, ",", expr mul_assoc, "]"] [],
  refine [expr mul_nonneg ihn _],
  generalize [] [":"] [expr «expr = »(«expr * »(«expr + »(1, 1), n), k)],
  cases [expr le_or_lt m k] ["with", ident hmk, ident hmk],
  { have [] [":", expr «expr ≤ »(m, «expr + »(k, 1))] [],
    from [expr hmk.trans (lt_add_one «expr↑ »(k)).le],
    exact [expr mul_nonneg_of_nonpos_of_nonpos (sub_nonpos_of_le hmk) (sub_nonpos_of_le this)] },
  { exact [expr mul_nonneg (sub_nonneg_of_le hmk.le) (sub_nonneg_of_le hmk)] }
end

theorem int_prod_range_pos {m : ℤ} {n : ℕ} (hn : Even n) (hm : m ∉ Ico (0 : ℤ) n) : 0 < ∏k in Finset.range n, m - k :=
  by 
    refine' (int_prod_range_nonneg m n hn).lt_of_ne fun h => hm _ 
    rw [eq_comm, Finset.prod_eq_zero_iff] at h 
    obtain ⟨a, ha, h⟩ := h 
    rw [sub_eq_zero.1 h]
    exact ⟨Int.coe_zero_le _, Int.coe_nat_lt.2$ Finset.mem_range.1 ha⟩

-- error in Analysis.Convex.SpecificFunctions: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- `x^m`, `m : ℤ` is convex on `(0, +∞)` for all `m` -/
theorem convex_on_zpow (m : exprℤ()) : convex_on exprℝ() (Ioi 0) (λ x : exprℝ(), «expr ^ »(x, m)) :=
begin
  have [] [":", expr ∀ n : exprℤ(), differentiable_on exprℝ() (λ x, «expr ^ »(x, n)) (Ioi (0 : exprℝ()))] [],
  from [expr λ n, differentiable_on_zpow _ _ «expr $ »(or.inl, lt_irrefl _)],
  apply [expr convex_on_of_deriv2_nonneg (convex_Ioi 0)]; try { simp [] [] ["only"] ["[", expr interior_Ioi, ",", expr deriv_zpow', "]"] [] [] },
  { exact [expr (this _).continuous_on] },
  { exact [expr this _] },
  { exact [expr (this _).const_mul _] },
  { intros [ident x, ident hx],
    simp [] [] ["only"] ["[", expr iter_deriv_zpow, ",", "<-", expr int.cast_coe_nat, ",", "<-", expr int.cast_sub, ",", "<-", expr int.cast_prod, "]"] [] [],
    refine [expr mul_nonneg (int.cast_nonneg.2 _) (zpow_nonneg (le_of_lt hx) _)],
    exact [expr int_prod_range_nonneg _ _ (nat.even_bit0 1)] }
end

-- error in Analysis.Convex.SpecificFunctions: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- `x^m`, `m : ℤ` is convex on `(0, +∞)` for all `m` except `0` and `1`. -/
theorem strict_convex_on_zpow
{m : exprℤ()}
(hm₀ : «expr ≠ »(m, 0))
(hm₁ : «expr ≠ »(m, 1)) : strict_convex_on exprℝ() (Ioi 0) (λ x : exprℝ(), «expr ^ »(x, m)) :=
begin
  have [] [":", expr ∀ n : exprℤ(), differentiable_on exprℝ() (λ x, «expr ^ »(x, n)) (Ioi (0 : exprℝ()))] [],
  from [expr λ n, differentiable_on_zpow _ _ «expr $ »(or.inl, lt_irrefl _)],
  apply [expr strict_convex_on_of_deriv2_pos (convex_Ioi 0)],
  { exact [expr (this _).continuous_on] },
  all_goals { rw [expr interior_Ioi] [] },
  { exact [expr this _] },
  intros [ident x, ident hx],
  simp [] [] ["only"] ["[", expr iter_deriv_zpow, ",", "<-", expr int.cast_coe_nat, ",", "<-", expr int.cast_sub, ",", "<-", expr int.cast_prod, "]"] [] [],
  refine [expr mul_pos (int.cast_pos.2 _) (zpow_pos_of_pos hx _)],
  refine [expr int_prod_range_pos (nat.even_bit0 1) (λ hm, _)],
  norm_cast ["at", ident hm],
  rw ["<-", expr finset.coe_Ico] ["at", ident hm],
  fin_cases [ident hm] [],
  { exact [expr hm₀ rfl] },
  { exact [expr hm₁ rfl] }
end

-- error in Analysis.Convex.SpecificFunctions: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem convex_on_rpow
{p : exprℝ()}
(hp : «expr ≤ »(1, p)) : convex_on exprℝ() (Ici 0) (λ x : exprℝ(), «expr ^ »(x, p)) :=
begin
  have [ident A] [":", expr «expr = »(deriv (λ
     x : exprℝ(), «expr ^ »(x, p)), λ x, «expr * »(p, «expr ^ »(x, «expr - »(p, 1))))] [],
  by { ext [] [ident x] [],
    simp [] [] [] ["[", expr hp, "]"] [] [] },
  apply [expr convex_on_of_deriv2_nonneg (convex_Ici 0)],
  { exact [expr continuous_on_id.rpow_const (λ x _, or.inr (zero_le_one.trans hp))] },
  { exact [expr (differentiable_rpow_const hp).differentiable_on] },
  { rw [expr A] [],
    assume [binders (x hx)],
    replace [ident hx] [":", expr «expr ≠ »(x, 0)] [],
    by { simp [] [] [] [] [] ["at", ident hx],
      exact [expr ne_of_gt hx] },
    simp [] [] [] ["[", expr differentiable_at.differentiable_within_at, ",", expr hx, "]"] [] [] },
  { assume [binders (x hx)],
    replace [ident hx] [":", expr «expr < »(0, x)] [],
    by simpa [] [] [] [] [] ["using", expr hx],
    suffices [] [":", expr «expr ≤ »(0, «expr * »(p, «expr * »(«expr - »(p, 1), «expr ^ »(x, «expr - »(«expr - »(p, 1), 1)))))],
    by simpa [] [] [] ["[", expr ne_of_gt hx, ",", expr A, "]"] [] [],
    apply [expr mul_nonneg (le_trans zero_le_one hp)],
    exact [expr mul_nonneg (sub_nonneg_of_le hp) (rpow_nonneg_of_nonneg hx.le _)] }
end

-- error in Analysis.Convex.SpecificFunctions: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem strict_convex_on_rpow
{p : exprℝ()}
(hp : «expr < »(1, p)) : strict_convex_on exprℝ() (Ici 0) (λ x : exprℝ(), «expr ^ »(x, p)) :=
begin
  have [ident A] [":", expr «expr = »(deriv (λ
     x : exprℝ(), «expr ^ »(x, p)), λ x, «expr * »(p, «expr ^ »(x, «expr - »(p, 1))))] [],
  by { ext [] [ident x] [],
    simp [] [] [] ["[", expr hp.le, "]"] [] [] },
  apply [expr strict_convex_on_of_deriv2_pos (convex_Ici 0)],
  { exact [expr continuous_on_id.rpow_const (λ x _, or.inr (zero_le_one.trans hp.le))] },
  { exact [expr (differentiable_rpow_const hp.le).differentiable_on] },
  rw [expr interior_Ici] [],
  rintro [ident x, "(", ident hx, ":", expr «expr < »(0, x), ")"],
  suffices [] [":", expr «expr < »(0, «expr * »(p, «expr * »(«expr - »(p, 1), «expr ^ »(x, «expr - »(«expr - »(p, 1), 1)))))],
  by simpa [] [] [] ["[", expr ne_of_gt hx, ",", expr A, "]"] [] [],
  exact [expr mul_pos (zero_lt_one.trans hp) (mul_pos (sub_pos_of_lt hp) (rpow_pos_of_pos hx _))]
end

-- error in Analysis.Convex.SpecificFunctions: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem strict_concave_on_log_Ioi : strict_concave_on exprℝ() (Ioi 0) log :=
begin
  have [ident h₁] [":", expr «expr ⊆ »(Ioi 0, «expr ᶜ»(({0} : set exprℝ())))] [],
  { exact [expr λ (x) (hx : «expr < »(0, x)) (hx' : «expr = »(x, 0)), hx.ne' hx'] },
  refine [expr strict_concave_on_open_of_deriv2_neg (convex_Ioi 0) is_open_Ioi (differentiable_on_log.mono h₁) (λ
    (x)
    (hx : «expr < »(0, x)), _)],
  rw ["[", expr function.iterate_succ, ",", expr function.iterate_one, "]"] [],
  change [expr «expr < »(deriv (deriv log) x, 0)] [] [],
  rw ["[", expr deriv_log', ",", expr deriv_inv, "]"] [],
  exact [expr neg_neg_of_pos «expr $ »(inv_pos.2, sq_pos_of_ne_zero _ hx.ne')]
end

-- error in Analysis.Convex.SpecificFunctions: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem strict_concave_on_log_Iio : strict_concave_on exprℝ() (Iio 0) log :=
begin
  have [ident h₁] [":", expr «expr ⊆ »(Iio 0, «expr ᶜ»(({0} : set exprℝ())))] [],
  { exact [expr λ (x) (hx : «expr < »(x, 0)) (hx' : «expr = »(x, 0)), hx.ne hx'] },
  refine [expr strict_concave_on_open_of_deriv2_neg (convex_Iio 0) is_open_Iio (differentiable_on_log.mono h₁) (λ
    (x)
    (hx : «expr < »(x, 0)), _)],
  rw ["[", expr function.iterate_succ, ",", expr function.iterate_one, "]"] [],
  change [expr «expr < »(deriv (deriv log) x, 0)] [] [],
  rw ["[", expr deriv_log', ",", expr deriv_inv, "]"] [],
  exact [expr neg_neg_of_pos «expr $ »(inv_pos.2, sq_pos_of_ne_zero _ hx.ne)]
end

