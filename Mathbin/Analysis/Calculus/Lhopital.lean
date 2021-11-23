import Mathbin.Analysis.Calculus.MeanValue

/-!
# L'Hôpital's rule for 0/0 indeterminate forms

In this file, we prove several forms of "L'Hopital's rule" for computing 0/0
indeterminate forms. The proof of `has_deriv_at.lhopital_zero_right_on_Ioo`
is based on the one given in the corresponding
[Wikibooks](https://en.wikibooks.org/wiki/Calculus/L%27H%C3%B4pital%27s_Rule)
chapter, and all other statements are derived from this one by composing by
carefully chosen functions.

Note that the filter `f'/g'` tends to isn't required to be one of `𝓝 a`,
`at_top` or `at_bot`. In fact, we give a slightly stronger statement by
allowing it to be any filter on `ℝ`.

Each statement is available in a `has_deriv_at` form and a `deriv` form, which
is denoted by each statement being in either the `has_deriv_at` or the `deriv`
namespace.

## Tags

L'Hôpital's rule, L'Hopital's rule
-/


open Filter Set

open_locale Filter TopologicalSpace Pointwise

variable{a b : ℝ}(hab : a < b){l : Filter ℝ}{f f' g g' : ℝ → ℝ}

/-!
## Interval-based versions

We start by proving statements where all conditions (derivability, `g' ≠ 0`) have
to be satisfied on an explicitly-provided interval.
-/


namespace HasDerivAt

include hab

-- error in Analysis.Calculus.Lhopital: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem lhopital_zero_right_on_Ioo
(hff' : ∀ x «expr ∈ » Ioo a b, has_deriv_at f (f' x) x)
(hgg' : ∀ x «expr ∈ » Ioo a b, has_deriv_at g (g' x) x)
(hg' : ∀ x «expr ∈ » Ioo a b, «expr ≠ »(g' x, 0))
(hfa : tendsto f «expr𝓝[ ] »(Ioi a, a) (expr𝓝() 0))
(hga : tendsto g «expr𝓝[ ] »(Ioi a, a) (expr𝓝() 0))
(hdiv : tendsto (λ
  x, «expr / »(f' x, g' x)) «expr𝓝[ ] »(Ioi a, a) l) : tendsto (λ x, «expr / »(f x, g x)) «expr𝓝[ ] »(Ioi a, a) l :=
begin
  have [ident sub] [":", expr ∀
   x «expr ∈ » Ioo a b, «expr ⊆ »(Ioo a x, Ioo a b)] [":=", expr λ x hx, Ioo_subset_Ioo (le_refl a) (le_of_lt hx.2)],
  have [ident hg] [":", expr ∀ x «expr ∈ » Ioo a b, «expr ≠ »(g x, 0)] [],
  { intros [ident x, ident hx, ident h],
    have [] [":", expr tendsto g «expr𝓝[ ] »(Iio x, x) (expr𝓝() 0)] [],
    { rw ["[", "<-", expr h, ",", "<-", expr nhds_within_Ioo_eq_nhds_within_Iio hx.1, "]"] [],
      exact [expr «expr $ »((hgg' x hx).continuous_at.continuous_within_at.mono, sub x hx).tendsto] },
    obtain ["⟨", ident y, ",", ident hyx, ",", ident hy, "⟩", ":", expr «expr∃ , »((c «expr ∈ » Ioo a x), «expr = »(g' c, 0))],
    from [expr exists_has_deriv_at_eq_zero' hx.1 hga this (λ y hy, «expr $ »(hgg' y, sub x hx hy))],
    exact [expr hg' y (sub x hx hyx) hy] },
  have [] [":", expr ∀
   x «expr ∈ » Ioo a b, «expr∃ , »((c «expr ∈ » Ioo a x), «expr = »(«expr * »(f x, g' c), «expr * »(g x, f' c)))] [],
  { intros [ident x, ident hx],
    rw ["[", "<-", expr sub_zero (f x), ",", "<-", expr sub_zero (g x), "]"] [],
    exact [expr exists_ratio_has_deriv_at_eq_ratio_slope' g g' hx.1 f f' (λ
      y
      hy, «expr $ »(hgg' y, sub x hx hy)) (λ
      y
      hy, «expr $ »(hff' y, sub x hx hy)) hga hfa (tendsto_nhds_within_of_tendsto_nhds (hgg' x hx).continuous_at.tendsto) (tendsto_nhds_within_of_tendsto_nhds (hff' x hx).continuous_at.tendsto)] },
  choose ["!"] [ident c] [ident hc] ["using", expr this],
  have [] [":", expr ∀
   x «expr ∈ » Ioo a b, «expr = »(«expr ∘ »(λ x', «expr / »(f' x', g' x'), c) x, «expr / »(f x, g x))] [],
  { intros [ident x, ident hx],
    rcases [expr hc x hx, "with", "⟨", ident h₁, ",", ident h₂, "⟩"],
    field_simp [] ["[", expr hg x hx, ",", expr hg' (c x) (sub x hx h₁), "]"] [] [],
    simp [] [] ["only"] ["[", expr h₂, "]"] [] [],
    rwa [expr mul_comm] [] },
  have [ident cmp] [":", expr ∀ x «expr ∈ » Ioo a b, «expr ∧ »(«expr < »(a, c x), «expr < »(c x, x))] [],
  from [expr λ x hx, (hc x hx).1],
  rw ["<-", expr nhds_within_Ioo_eq_nhds_within_Ioi hab] [],
  apply [expr tendsto_nhds_within_congr this],
  simp [] [] ["only"] [] [] [],
  apply [expr hdiv.comp],
  refine [expr tendsto_nhds_within_of_tendsto_nhds_of_eventually_within _ (tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds (tendsto_nhds_within_of_tendsto_nhds tendsto_id) _ _) _],
  all_goals { apply [expr eventually_nhds_with_of_forall],
    intros [ident x, ident hx],
    have [] [] [":=", expr cmp x hx],
    try { simp [] [] [] [] [] [] },
    linarith [] [] ["[", expr this, "]"] }
end

theorem lhopital_zero_right_on_Ico (hff' : ∀ x _ : x ∈ Ioo a b, HasDerivAt f (f' x) x)
  (hgg' : ∀ x _ : x ∈ Ioo a b, HasDerivAt g (g' x) x) (hcf : ContinuousOn f (Ico a b)) (hcg : ContinuousOn g (Ico a b))
  (hg' : ∀ x _ : x ∈ Ioo a b, g' x ≠ 0) (hfa : f a = 0) (hga : g a = 0)
  (hdiv : tendsto (fun x => f' x / g' x) (nhdsWithin a (Ioi a)) l) :
  tendsto (fun x => f x / g x) (nhdsWithin a (Ioi a)) l :=
  by 
    refine' lhopital_zero_right_on_Ioo hab hff' hgg' hg' _ _ hdiv
    ·
      rw [←hfa, ←nhds_within_Ioo_eq_nhds_within_Ioi hab]
      exact ((hcf a$ left_mem_Ico.mpr hab).mono Ioo_subset_Ico_self).Tendsto
    ·
      rw [←hga, ←nhds_within_Ioo_eq_nhds_within_Ioi hab]
      exact ((hcg a$ left_mem_Ico.mpr hab).mono Ioo_subset_Ico_self).Tendsto

-- error in Analysis.Calculus.Lhopital: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem lhopital_zero_left_on_Ioo
(hff' : ∀ x «expr ∈ » Ioo a b, has_deriv_at f (f' x) x)
(hgg' : ∀ x «expr ∈ » Ioo a b, has_deriv_at g (g' x) x)
(hg' : ∀ x «expr ∈ » Ioo a b, «expr ≠ »(g' x, 0))
(hfb : tendsto f (nhds_within b (Iio b)) (expr𝓝() 0))
(hgb : tendsto g (nhds_within b (Iio b)) (expr𝓝() 0))
(hdiv : tendsto (λ
  x, «expr / »(f' x, g' x)) (nhds_within b (Iio b)) l) : tendsto (λ x, «expr / »(f x, g x)) (nhds_within b (Iio b)) l :=
begin
  have [ident hdnf] [":", expr ∀
   x «expr ∈ » «expr- »(Ioo a b), has_deriv_at «expr ∘ »(f, has_neg.neg) «expr * »(f' «expr- »(x), «expr- »(1)) x] [],
  from [expr λ x hx, comp x (hff' «expr- »(x) hx) (has_deriv_at_neg x)],
  have [ident hdng] [":", expr ∀
   x «expr ∈ » «expr- »(Ioo a b), has_deriv_at «expr ∘ »(g, has_neg.neg) «expr * »(g' «expr- »(x), «expr- »(1)) x] [],
  from [expr λ x hx, comp x (hgg' «expr- »(x) hx) (has_deriv_at_neg x)],
  rw [expr preimage_neg_Ioo] ["at", ident hdnf],
  rw [expr preimage_neg_Ioo] ["at", ident hdng],
  have [] [] [":=", expr lhopital_zero_right_on_Ioo (neg_lt_neg hab) hdnf hdng (by { intros [ident x, ident hx, ident h],
      apply [expr hg' _ (by { rw ["<-", expr preimage_neg_Ioo] ["at", ident hx], exact [expr hx] })],
      rwa ["[", expr mul_comm, ",", "<-", expr neg_eq_neg_one_mul, ",", expr neg_eq_zero, "]"] ["at", ident h] }) (hfb.comp tendsto_neg_nhds_within_Ioi_neg) (hgb.comp tendsto_neg_nhds_within_Ioi_neg) (by { simp [] [] ["only"] ["[", expr neg_div_neg_eq, ",", expr mul_one, ",", expr mul_neg_eq_neg_mul_symm, "]"] [] [],
      exact [expr «expr $ »(tendsto_congr, λ x, rfl).mp (hdiv.comp tendsto_neg_nhds_within_Ioi_neg)] })],
  have [] [] [":=", expr this.comp tendsto_neg_nhds_within_Iio],
  unfold [ident function.comp] ["at", ident this],
  simpa [] [] ["only"] ["[", expr neg_neg, "]"] [] []
end

theorem lhopital_zero_left_on_Ioc (hff' : ∀ x _ : x ∈ Ioo a b, HasDerivAt f (f' x) x)
  (hgg' : ∀ x _ : x ∈ Ioo a b, HasDerivAt g (g' x) x) (hcf : ContinuousOn f (Ioc a b)) (hcg : ContinuousOn g (Ioc a b))
  (hg' : ∀ x _ : x ∈ Ioo a b, g' x ≠ 0) (hfb : f b = 0) (hgb : g b = 0)
  (hdiv : tendsto (fun x => f' x / g' x) (nhdsWithin b (Iio b)) l) :
  tendsto (fun x => f x / g x) (nhdsWithin b (Iio b)) l :=
  by 
    refine' lhopital_zero_left_on_Ioo hab hff' hgg' hg' _ _ hdiv
    ·
      rw [←hfb, ←nhds_within_Ioo_eq_nhds_within_Iio hab]
      exact ((hcf b$ right_mem_Ioc.mpr hab).mono Ioo_subset_Ioc_self).Tendsto
    ·
      rw [←hgb, ←nhds_within_Ioo_eq_nhds_within_Iio hab]
      exact ((hcg b$ right_mem_Ioc.mpr hab).mono Ioo_subset_Ioc_self).Tendsto

omit hab

-- error in Analysis.Calculus.Lhopital: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem lhopital_zero_at_top_on_Ioi
(hff' : ∀ x «expr ∈ » Ioi a, has_deriv_at f (f' x) x)
(hgg' : ∀ x «expr ∈ » Ioi a, has_deriv_at g (g' x) x)
(hg' : ∀ x «expr ∈ » Ioi a, «expr ≠ »(g' x, 0))
(hftop : tendsto f at_top (expr𝓝() 0))
(hgtop : tendsto g at_top (expr𝓝() 0))
(hdiv : tendsto (λ x, «expr / »(f' x, g' x)) at_top l) : tendsto (λ x, «expr / »(f x, g x)) at_top l :=
begin
  obtain ["⟨", ident a', ",", ident haa', ",", ident ha', "⟩", ":", expr «expr∃ , »((a'), «expr ∧ »(«expr < »(a, a'), «expr < »(0, a'))), ":=", expr ⟨«expr + »(1, max a 0), ⟨lt_of_le_of_lt (le_max_left a 0) (lt_one_add _), lt_of_le_of_lt (le_max_right a 0) (lt_one_add _)⟩⟩],
  have [ident fact1] [":", expr ∀
   x : exprℝ(), «expr ∈ »(x, Ioo 0 «expr ⁻¹»(a')) → «expr ≠ »(x, 0)] [":=", expr λ _ hx, (ne_of_lt hx.1).symm],
  have [ident fact2] [":", expr ∀ x «expr ∈ » Ioo 0 «expr ⁻¹»(a'), «expr < »(a, «expr ⁻¹»(x))] [],
  from [expr λ _ hx, lt_trans haa' ((lt_inv ha' hx.1).mpr hx.2)],
  have [ident hdnf] [":", expr ∀
   x «expr ∈ » Ioo 0 «expr ⁻¹»(a'), has_deriv_at «expr ∘ »(f, has_inv.inv) «expr * »(f' «expr ⁻¹»(x), «expr- »(«expr ⁻¹»(«expr ^ »(x, 2)))) x] [],
  from [expr λ x hx, comp x «expr $ »(hff' «expr ⁻¹»(x), fact2 x hx) «expr $ »(has_deriv_at_inv, fact1 x hx)],
  have [ident hdng] [":", expr ∀
   x «expr ∈ » Ioo 0 «expr ⁻¹»(a'), has_deriv_at «expr ∘ »(g, has_inv.inv) «expr * »(g' «expr ⁻¹»(x), «expr- »(«expr ⁻¹»(«expr ^ »(x, 2)))) x] [],
  from [expr λ x hx, comp x «expr $ »(hgg' «expr ⁻¹»(x), fact2 x hx) «expr $ »(has_deriv_at_inv, fact1 x hx)],
  have [] [] [":=", expr lhopital_zero_right_on_Ioo (inv_pos.mpr ha') hdnf hdng (by { intros [ident x, ident hx],
      refine [expr mul_ne_zero _ «expr $ »(neg_ne_zero.mpr, «expr $ »(inv_ne_zero, «expr $ »(pow_ne_zero _, fact1 x hx)))],
      exact [expr hg' _ (fact2 x hx)] }) (hftop.comp tendsto_inv_zero_at_top) (hgtop.comp tendsto_inv_zero_at_top) (by { refine [expr (tendsto_congr' _).mp (hdiv.comp tendsto_inv_zero_at_top)],
      rw [expr eventually_eq_iff_exists_mem] [],
      use ["[", expr Ioi 0, ",", expr self_mem_nhds_within, "]"],
      intros [ident x, ident hx],
      unfold [ident function.comp] [],
      erw [expr mul_div_mul_right] [],
      refine [expr neg_ne_zero.mpr «expr $ »(inv_ne_zero, «expr $ »(pow_ne_zero _, ne_of_gt hx))] })],
  have [] [] [":=", expr this.comp tendsto_inv_at_top_zero'],
  unfold [ident function.comp] ["at", ident this],
  simpa [] [] ["only"] ["[", expr inv_inv₀, "]"] [] []
end

-- error in Analysis.Calculus.Lhopital: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem lhopital_zero_at_bot_on_Iio
(hff' : ∀ x «expr ∈ » Iio a, has_deriv_at f (f' x) x)
(hgg' : ∀ x «expr ∈ » Iio a, has_deriv_at g (g' x) x)
(hg' : ∀ x «expr ∈ » Iio a, «expr ≠ »(g' x, 0))
(hfbot : tendsto f at_bot (expr𝓝() 0))
(hgbot : tendsto g at_bot (expr𝓝() 0))
(hdiv : tendsto (λ x, «expr / »(f' x, g' x)) at_bot l) : tendsto (λ x, «expr / »(f x, g x)) at_bot l :=
begin
  have [ident hdnf] [":", expr ∀
   x «expr ∈ » «expr- »(Iio a), has_deriv_at «expr ∘ »(f, has_neg.neg) «expr * »(f' «expr- »(x), «expr- »(1)) x] [],
  from [expr λ x hx, comp x (hff' «expr- »(x) hx) (has_deriv_at_neg x)],
  have [ident hdng] [":", expr ∀
   x «expr ∈ » «expr- »(Iio a), has_deriv_at «expr ∘ »(g, has_neg.neg) «expr * »(g' «expr- »(x), «expr- »(1)) x] [],
  from [expr λ x hx, comp x (hgg' «expr- »(x) hx) (has_deriv_at_neg x)],
  rw [expr preimage_neg_Iio] ["at", ident hdnf],
  rw [expr preimage_neg_Iio] ["at", ident hdng],
  have [] [] [":=", expr lhopital_zero_at_top_on_Ioi hdnf hdng (by { intros [ident x, ident hx, ident h],
      apply [expr hg' _ (by { rw ["<-", expr preimage_neg_Iio] ["at", ident hx], exact [expr hx] })],
      rwa ["[", expr mul_comm, ",", "<-", expr neg_eq_neg_one_mul, ",", expr neg_eq_zero, "]"] ["at", ident h] }) (hfbot.comp tendsto_neg_at_top_at_bot) (hgbot.comp tendsto_neg_at_top_at_bot) (by { simp [] [] ["only"] ["[", expr mul_one, ",", expr mul_neg_eq_neg_mul_symm, ",", expr neg_div_neg_eq, "]"] [] [],
      exact [expr «expr $ »(tendsto_congr, λ x, rfl).mp (hdiv.comp tendsto_neg_at_top_at_bot)] })],
  have [] [] [":=", expr this.comp tendsto_neg_at_bot_at_top],
  unfold [ident function.comp] ["at", ident this],
  simpa [] [] ["only"] ["[", expr neg_neg, "]"] [] []
end

end HasDerivAt

namespace deriv

include hab

-- error in Analysis.Calculus.Lhopital: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem lhopital_zero_right_on_Ioo
(hdf : differentiable_on exprℝ() f (Ioo a b))
(hg' : ∀ x «expr ∈ » Ioo a b, «expr ≠ »(deriv g x, 0))
(hfa : tendsto f «expr𝓝[ ] »(Ioi a, a) (expr𝓝() 0))
(hga : tendsto g «expr𝓝[ ] »(Ioi a, a) (expr𝓝() 0))
(hdiv : tendsto (λ
  x, «expr / »(deriv f x, deriv g x)) «expr𝓝[ ] »(Ioi a, a) l) : tendsto (λ
 x, «expr / »(f x, g x)) «expr𝓝[ ] »(Ioi a, a) l :=
begin
  have [ident hdf] [":", expr ∀ x «expr ∈ » Ioo a b, differentiable_at exprℝ() f x] [],
  from [expr λ x hx, (hdf x hx).differentiable_at (Ioo_mem_nhds hx.1 hx.2)],
  have [ident hdg] [":", expr ∀ x «expr ∈ » Ioo a b, differentiable_at exprℝ() g x] [],
  from [expr λ x hx, classical.by_contradiction (λ h, hg' x hx (deriv_zero_of_not_differentiable_at h))],
  exact [expr has_deriv_at.lhopital_zero_right_on_Ioo hab (λ
    x hx, (hdf x hx).has_deriv_at) (λ x hx, (hdg x hx).has_deriv_at) hg' hfa hga hdiv]
end

theorem lhopital_zero_right_on_Ico (hdf : DifferentiableOn ℝ f (Ioo a b)) (hcf : ContinuousOn f (Ico a b))
  (hcg : ContinuousOn g (Ico a b)) (hg' : ∀ x _ : x ∈ Ioo a b, (deriv g) x ≠ 0) (hfa : f a = 0) (hga : g a = 0)
  (hdiv : tendsto (fun x => (deriv f) x / (deriv g) x) (nhdsWithin a (Ioi a)) l) :
  tendsto (fun x => f x / g x) (nhdsWithin a (Ioi a)) l :=
  by 
    refine' lhopital_zero_right_on_Ioo hab hdf hg' _ _ hdiv
    ·
      rw [←hfa, ←nhds_within_Ioo_eq_nhds_within_Ioi hab]
      exact ((hcf a$ left_mem_Ico.mpr hab).mono Ioo_subset_Ico_self).Tendsto
    ·
      rw [←hga, ←nhds_within_Ioo_eq_nhds_within_Ioi hab]
      exact ((hcg a$ left_mem_Ico.mpr hab).mono Ioo_subset_Ico_self).Tendsto

-- error in Analysis.Calculus.Lhopital: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem lhopital_zero_left_on_Ioo
(hdf : differentiable_on exprℝ() f (Ioo a b))
(hg' : ∀ x «expr ∈ » Ioo a b, «expr ≠ »(deriv g x, 0))
(hfb : tendsto f (nhds_within b (Iio b)) (expr𝓝() 0))
(hgb : tendsto g (nhds_within b (Iio b)) (expr𝓝() 0))
(hdiv : tendsto (λ
  x, «expr / »(deriv f x, deriv g x)) (nhds_within b (Iio b)) l) : tendsto (λ
 x, «expr / »(f x, g x)) (nhds_within b (Iio b)) l :=
begin
  have [ident hdf] [":", expr ∀ x «expr ∈ » Ioo a b, differentiable_at exprℝ() f x] [],
  from [expr λ x hx, (hdf x hx).differentiable_at (Ioo_mem_nhds hx.1 hx.2)],
  have [ident hdg] [":", expr ∀ x «expr ∈ » Ioo a b, differentiable_at exprℝ() g x] [],
  from [expr λ x hx, classical.by_contradiction (λ h, hg' x hx (deriv_zero_of_not_differentiable_at h))],
  exact [expr has_deriv_at.lhopital_zero_left_on_Ioo hab (λ
    x hx, (hdf x hx).has_deriv_at) (λ x hx, (hdg x hx).has_deriv_at) hg' hfb hgb hdiv]
end

omit hab

-- error in Analysis.Calculus.Lhopital: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem lhopital_zero_at_top_on_Ioi
(hdf : differentiable_on exprℝ() f (Ioi a))
(hg' : ∀ x «expr ∈ » Ioi a, «expr ≠ »(deriv g x, 0))
(hftop : tendsto f at_top (expr𝓝() 0))
(hgtop : tendsto g at_top (expr𝓝() 0))
(hdiv : tendsto (λ x, «expr / »(deriv f x, deriv g x)) at_top l) : tendsto (λ x, «expr / »(f x, g x)) at_top l :=
begin
  have [ident hdf] [":", expr ∀ x «expr ∈ » Ioi a, differentiable_at exprℝ() f x] [],
  from [expr λ x hx, (hdf x hx).differentiable_at (Ioi_mem_nhds hx)],
  have [ident hdg] [":", expr ∀ x «expr ∈ » Ioi a, differentiable_at exprℝ() g x] [],
  from [expr λ x hx, classical.by_contradiction (λ h, hg' x hx (deriv_zero_of_not_differentiable_at h))],
  exact [expr has_deriv_at.lhopital_zero_at_top_on_Ioi (λ
    x hx, (hdf x hx).has_deriv_at) (λ x hx, (hdg x hx).has_deriv_at) hg' hftop hgtop hdiv]
end

-- error in Analysis.Calculus.Lhopital: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem lhopital_zero_at_bot_on_Iio
(hdf : differentiable_on exprℝ() f (Iio a))
(hg' : ∀ x «expr ∈ » Iio a, «expr ≠ »(deriv g x, 0))
(hfbot : tendsto f at_bot (expr𝓝() 0))
(hgbot : tendsto g at_bot (expr𝓝() 0))
(hdiv : tendsto (λ x, «expr / »(deriv f x, deriv g x)) at_bot l) : tendsto (λ x, «expr / »(f x, g x)) at_bot l :=
begin
  have [ident hdf] [":", expr ∀ x «expr ∈ » Iio a, differentiable_at exprℝ() f x] [],
  from [expr λ x hx, (hdf x hx).differentiable_at (Iio_mem_nhds hx)],
  have [ident hdg] [":", expr ∀ x «expr ∈ » Iio a, differentiable_at exprℝ() g x] [],
  from [expr λ x hx, classical.by_contradiction (λ h, hg' x hx (deriv_zero_of_not_differentiable_at h))],
  exact [expr has_deriv_at.lhopital_zero_at_bot_on_Iio (λ
    x hx, (hdf x hx).has_deriv_at) (λ x hx, (hdg x hx).has_deriv_at) hg' hfbot hgbot hdiv]
end

end deriv

/-!
## Generic versions

The following statements no longer any explicit interval, as they only require
conditions holding eventually.
-/


namespace HasDerivAt

-- error in Analysis.Calculus.Lhopital: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- L'Hôpital's rule for approaching a real from the right, `has_deriv_at` version -/
theorem lhopital_zero_nhds_right
(hff' : «expr∀ᶠ in , »((x), «expr𝓝[ ] »(Ioi a, a), has_deriv_at f (f' x) x))
(hgg' : «expr∀ᶠ in , »((x), «expr𝓝[ ] »(Ioi a, a), has_deriv_at g (g' x) x))
(hg' : «expr∀ᶠ in , »((x), «expr𝓝[ ] »(Ioi a, a), «expr ≠ »(g' x, 0)))
(hfa : tendsto f «expr𝓝[ ] »(Ioi a, a) (expr𝓝() 0))
(hga : tendsto g «expr𝓝[ ] »(Ioi a, a) (expr𝓝() 0))
(hdiv : tendsto (λ
  x, «expr / »(f' x, g' x)) «expr𝓝[ ] »(Ioi a, a) l) : tendsto (λ x, «expr / »(f x, g x)) «expr𝓝[ ] »(Ioi a, a) l :=
begin
  rw [expr eventually_iff_exists_mem] ["at", "*"],
  rcases [expr hff', "with", "⟨", ident s₁, ",", ident hs₁, ",", ident hff', "⟩"],
  rcases [expr hgg', "with", "⟨", ident s₂, ",", ident hs₂, ",", ident hgg', "⟩"],
  rcases [expr hg', "with", "⟨", ident s₃, ",", ident hs₃, ",", ident hg', "⟩"],
  let [ident s] [] [":=", expr «expr ∩ »(«expr ∩ »(s₁, s₂), s₃)],
  have [ident hs] [":", expr «expr ∈ »(s, «expr𝓝[ ] »(Ioi a, a))] [":=", expr inter_mem (inter_mem hs₁ hs₂) hs₃],
  rw [expr mem_nhds_within_Ioi_iff_exists_Ioo_subset] ["at", ident hs],
  rcases [expr hs, "with", "⟨", ident u, ",", ident hau, ",", ident hu, "⟩"],
  refine [expr lhopital_zero_right_on_Ioo hau _ _ _ hfa hga hdiv]; intros [ident x, ident hx]; apply_assumption; exact [expr (hu hx).1.1] <|> exact [expr (hu hx).1.2] <|> exact [expr (hu hx).2]
end

-- error in Analysis.Calculus.Lhopital: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- L'Hôpital's rule for approaching a real from the left, `has_deriv_at` version -/
theorem lhopital_zero_nhds_left
(hff' : «expr∀ᶠ in , »((x), «expr𝓝[ ] »(Iio a, a), has_deriv_at f (f' x) x))
(hgg' : «expr∀ᶠ in , »((x), «expr𝓝[ ] »(Iio a, a), has_deriv_at g (g' x) x))
(hg' : «expr∀ᶠ in , »((x), «expr𝓝[ ] »(Iio a, a), «expr ≠ »(g' x, 0)))
(hfa : tendsto f «expr𝓝[ ] »(Iio a, a) (expr𝓝() 0))
(hga : tendsto g «expr𝓝[ ] »(Iio a, a) (expr𝓝() 0))
(hdiv : tendsto (λ
  x, «expr / »(f' x, g' x)) «expr𝓝[ ] »(Iio a, a) l) : tendsto (λ x, «expr / »(f x, g x)) «expr𝓝[ ] »(Iio a, a) l :=
begin
  rw [expr eventually_iff_exists_mem] ["at", "*"],
  rcases [expr hff', "with", "⟨", ident s₁, ",", ident hs₁, ",", ident hff', "⟩"],
  rcases [expr hgg', "with", "⟨", ident s₂, ",", ident hs₂, ",", ident hgg', "⟩"],
  rcases [expr hg', "with", "⟨", ident s₃, ",", ident hs₃, ",", ident hg', "⟩"],
  let [ident s] [] [":=", expr «expr ∩ »(«expr ∩ »(s₁, s₂), s₃)],
  have [ident hs] [":", expr «expr ∈ »(s, «expr𝓝[ ] »(Iio a, a))] [":=", expr inter_mem (inter_mem hs₁ hs₂) hs₃],
  rw [expr mem_nhds_within_Iio_iff_exists_Ioo_subset] ["at", ident hs],
  rcases [expr hs, "with", "⟨", ident l, ",", ident hal, ",", ident hl, "⟩"],
  refine [expr lhopital_zero_left_on_Ioo hal _ _ _ hfa hga hdiv]; intros [ident x, ident hx]; apply_assumption; exact [expr (hl hx).1.1] <|> exact [expr (hl hx).1.2] <|> exact [expr (hl hx).2]
end

-- error in Analysis.Calculus.Lhopital: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- L'Hôpital's rule for approaching a real, `has_deriv_at` version. This
  does not require anything about the situation at `a` -/
theorem lhopital_zero_nhds'
(hff' : «expr∀ᶠ in , »((x), «expr𝓝[ ] »(«expr \ »(univ, {a}), a), has_deriv_at f (f' x) x))
(hgg' : «expr∀ᶠ in , »((x), «expr𝓝[ ] »(«expr \ »(univ, {a}), a), has_deriv_at g (g' x) x))
(hg' : «expr∀ᶠ in , »((x), «expr𝓝[ ] »(«expr \ »(univ, {a}), a), «expr ≠ »(g' x, 0)))
(hfa : tendsto f «expr𝓝[ ] »(«expr \ »(univ, {a}), a) (expr𝓝() 0))
(hga : tendsto g «expr𝓝[ ] »(«expr \ »(univ, {a}), a) (expr𝓝() 0))
(hdiv : tendsto (λ
  x, «expr / »(f' x, g' x)) «expr𝓝[ ] »(«expr \ »(univ, {a}), a) l) : tendsto (λ
 x, «expr / »(f x, g x)) «expr𝓝[ ] »(«expr \ »(univ, {a}), a) l :=
begin
  have [] [":", expr «expr = »(«expr \ »(univ, {a}), «expr ∪ »(Iio a, Ioi a))] [],
  { ext [] [] [],
    rw ["[", expr mem_diff_singleton, ",", expr «expr $ »(eq_true_intro, mem_univ x), ",", expr true_and, ",", expr ne_iff_lt_or_gt, "]"] [],
    refl },
  simp [] [] ["only"] ["[", expr this, ",", expr nhds_within_union, ",", expr tendsto_sup, ",", expr eventually_sup, "]"] [] ["at", "*"],
  exact [expr ⟨lhopital_zero_nhds_left hff'.1 hgg'.1 hg'.1 hfa.1 hga.1 hdiv.1, lhopital_zero_nhds_right hff'.2 hgg'.2 hg'.2 hfa.2 hga.2 hdiv.2⟩]
end

/-- **L'Hôpital's rule** for approaching a real, `has_deriv_at` version -/
theorem lhopital_zero_nhds (hff' : ∀ᶠx in 𝓝 a, HasDerivAt f (f' x) x) (hgg' : ∀ᶠx in 𝓝 a, HasDerivAt g (g' x) x)
  (hg' : ∀ᶠx in 𝓝 a, g' x ≠ 0) (hfa : tendsto f (𝓝 a) (𝓝 0)) (hga : tendsto g (𝓝 a) (𝓝 0))
  (hdiv : tendsto (fun x => f' x / g' x) (𝓝 a) l) : tendsto (fun x => f x / g x) (𝓝[univ \ {a}] a) l :=
  by 
    apply @lhopital_zero_nhds' _ _ _ f' _ g' <;>
      first |
          apply eventually_nhds_within_of_eventually_nhds|
          apply tendsto_nhds_within_of_tendsto_nhds <;>
        assumption

-- error in Analysis.Calculus.Lhopital: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- L'Hôpital's rule for approaching +∞, `has_deriv_at` version -/
theorem lhopital_zero_at_top
(hff' : «expr∀ᶠ in , »((x), at_top, has_deriv_at f (f' x) x))
(hgg' : «expr∀ᶠ in , »((x), at_top, has_deriv_at g (g' x) x))
(hg' : «expr∀ᶠ in , »((x), at_top, «expr ≠ »(g' x, 0)))
(hftop : tendsto f at_top (expr𝓝() 0))
(hgtop : tendsto g at_top (expr𝓝() 0))
(hdiv : tendsto (λ x, «expr / »(f' x, g' x)) at_top l) : tendsto (λ x, «expr / »(f x, g x)) at_top l :=
begin
  rw [expr eventually_iff_exists_mem] ["at", "*"],
  rcases [expr hff', "with", "⟨", ident s₁, ",", ident hs₁, ",", ident hff', "⟩"],
  rcases [expr hgg', "with", "⟨", ident s₂, ",", ident hs₂, ",", ident hgg', "⟩"],
  rcases [expr hg', "with", "⟨", ident s₃, ",", ident hs₃, ",", ident hg', "⟩"],
  let [ident s] [] [":=", expr «expr ∩ »(«expr ∩ »(s₁, s₂), s₃)],
  have [ident hs] [":", expr «expr ∈ »(s, at_top)] [":=", expr inter_mem (inter_mem hs₁ hs₂) hs₃],
  rw [expr mem_at_top_sets] ["at", ident hs],
  rcases [expr hs, "with", "⟨", ident l, ",", ident hl, "⟩"],
  have [ident hl'] [":", expr «expr ⊆ »(Ioi l, s)] [":=", expr λ x hx, hl x (le_of_lt hx)],
  refine [expr lhopital_zero_at_top_on_Ioi _ _ (λ
    x
    hx, «expr $ »(hg' x, (hl' hx).2)) hftop hgtop hdiv]; intros [ident x, ident hx]; apply_assumption; exact [expr (hl' hx).1.1] <|> exact [expr (hl' hx).1.2]
end

-- error in Analysis.Calculus.Lhopital: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- L'Hôpital's rule for approaching -∞, `has_deriv_at` version -/
theorem lhopital_zero_at_bot
(hff' : «expr∀ᶠ in , »((x), at_bot, has_deriv_at f (f' x) x))
(hgg' : «expr∀ᶠ in , »((x), at_bot, has_deriv_at g (g' x) x))
(hg' : «expr∀ᶠ in , »((x), at_bot, «expr ≠ »(g' x, 0)))
(hfbot : tendsto f at_bot (expr𝓝() 0))
(hgbot : tendsto g at_bot (expr𝓝() 0))
(hdiv : tendsto (λ x, «expr / »(f' x, g' x)) at_bot l) : tendsto (λ x, «expr / »(f x, g x)) at_bot l :=
begin
  rw [expr eventually_iff_exists_mem] ["at", "*"],
  rcases [expr hff', "with", "⟨", ident s₁, ",", ident hs₁, ",", ident hff', "⟩"],
  rcases [expr hgg', "with", "⟨", ident s₂, ",", ident hs₂, ",", ident hgg', "⟩"],
  rcases [expr hg', "with", "⟨", ident s₃, ",", ident hs₃, ",", ident hg', "⟩"],
  let [ident s] [] [":=", expr «expr ∩ »(«expr ∩ »(s₁, s₂), s₃)],
  have [ident hs] [":", expr «expr ∈ »(s, at_bot)] [":=", expr inter_mem (inter_mem hs₁ hs₂) hs₃],
  rw [expr mem_at_bot_sets] ["at", ident hs],
  rcases [expr hs, "with", "⟨", ident l, ",", ident hl, "⟩"],
  have [ident hl'] [":", expr «expr ⊆ »(Iio l, s)] [":=", expr λ x hx, hl x (le_of_lt hx)],
  refine [expr lhopital_zero_at_bot_on_Iio _ _ (λ
    x
    hx, «expr $ »(hg' x, (hl' hx).2)) hfbot hgbot hdiv]; intros [ident x, ident hx]; apply_assumption; exact [expr (hl' hx).1.1] <|> exact [expr (hl' hx).1.2]
end

end HasDerivAt

namespace deriv

-- error in Analysis.Calculus.Lhopital: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- **L'Hôpital's rule** for approaching a real from the right, `deriv` version -/
theorem lhopital_zero_nhds_right
(hdf : «expr∀ᶠ in , »((x), «expr𝓝[ ] »(Ioi a, a), differentiable_at exprℝ() f x))
(hg' : «expr∀ᶠ in , »((x), «expr𝓝[ ] »(Ioi a, a), «expr ≠ »(deriv g x, 0)))
(hfa : tendsto f «expr𝓝[ ] »(Ioi a, a) (expr𝓝() 0))
(hga : tendsto g «expr𝓝[ ] »(Ioi a, a) (expr𝓝() 0))
(hdiv : tendsto (λ
  x, «expr / »(deriv f x, deriv g x)) «expr𝓝[ ] »(Ioi a, a) l) : tendsto (λ
 x, «expr / »(f x, g x)) «expr𝓝[ ] »(Ioi a, a) l :=
begin
  have [ident hdg] [":", expr «expr∀ᶠ in , »((x), «expr𝓝[ ] »(Ioi a, a), differentiable_at exprℝ() g x)] [],
  from [expr hg'.mp «expr $ »(eventually_of_forall, λ
    _ hg', classical.by_contradiction (λ h, hg' (deriv_zero_of_not_differentiable_at h)))],
  have [ident hdf'] [":", expr «expr∀ᶠ in , »((x), «expr𝓝[ ] »(Ioi a, a), has_deriv_at f (deriv f x) x)] [],
  from [expr hdf.mp «expr $ »(eventually_of_forall, λ _, differentiable_at.has_deriv_at)],
  have [ident hdg'] [":", expr «expr∀ᶠ in , »((x), «expr𝓝[ ] »(Ioi a, a), has_deriv_at g (deriv g x) x)] [],
  from [expr hdg.mp «expr $ »(eventually_of_forall, λ _, differentiable_at.has_deriv_at)],
  exact [expr has_deriv_at.lhopital_zero_nhds_right hdf' hdg' hg' hfa hga hdiv]
end

-- error in Analysis.Calculus.Lhopital: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- **L'Hôpital's rule** for approaching a real from the left, `deriv` version -/
theorem lhopital_zero_nhds_left
(hdf : «expr∀ᶠ in , »((x), «expr𝓝[ ] »(Iio a, a), differentiable_at exprℝ() f x))
(hg' : «expr∀ᶠ in , »((x), «expr𝓝[ ] »(Iio a, a), «expr ≠ »(deriv g x, 0)))
(hfa : tendsto f «expr𝓝[ ] »(Iio a, a) (expr𝓝() 0))
(hga : tendsto g «expr𝓝[ ] »(Iio a, a) (expr𝓝() 0))
(hdiv : tendsto (λ
  x, «expr / »(deriv f x, deriv g x)) «expr𝓝[ ] »(Iio a, a) l) : tendsto (λ
 x, «expr / »(f x, g x)) «expr𝓝[ ] »(Iio a, a) l :=
begin
  have [ident hdg] [":", expr «expr∀ᶠ in , »((x), «expr𝓝[ ] »(Iio a, a), differentiable_at exprℝ() g x)] [],
  from [expr hg'.mp «expr $ »(eventually_of_forall, λ
    _ hg', classical.by_contradiction (λ h, hg' (deriv_zero_of_not_differentiable_at h)))],
  have [ident hdf'] [":", expr «expr∀ᶠ in , »((x), «expr𝓝[ ] »(Iio a, a), has_deriv_at f (deriv f x) x)] [],
  from [expr hdf.mp «expr $ »(eventually_of_forall, λ _, differentiable_at.has_deriv_at)],
  have [ident hdg'] [":", expr «expr∀ᶠ in , »((x), «expr𝓝[ ] »(Iio a, a), has_deriv_at g (deriv g x) x)] [],
  from [expr hdg.mp «expr $ »(eventually_of_forall, λ _, differentiable_at.has_deriv_at)],
  exact [expr has_deriv_at.lhopital_zero_nhds_left hdf' hdg' hg' hfa hga hdiv]
end

-- error in Analysis.Calculus.Lhopital: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- **L'Hôpital's rule** for approaching a real, `deriv` version. This
  does not require anything about the situation at `a` -/
theorem lhopital_zero_nhds'
(hdf : «expr∀ᶠ in , »((x), «expr𝓝[ ] »(«expr \ »(univ, {a}), a), differentiable_at exprℝ() f x))
(hg' : «expr∀ᶠ in , »((x), «expr𝓝[ ] »(«expr \ »(univ, {a}), a), «expr ≠ »(deriv g x, 0)))
(hfa : tendsto f «expr𝓝[ ] »(«expr \ »(univ, {a}), a) (expr𝓝() 0))
(hga : tendsto g «expr𝓝[ ] »(«expr \ »(univ, {a}), a) (expr𝓝() 0))
(hdiv : tendsto (λ
  x, «expr / »(deriv f x, deriv g x)) «expr𝓝[ ] »(«expr \ »(univ, {a}), a) l) : tendsto (λ
 x, «expr / »(f x, g x)) «expr𝓝[ ] »(«expr \ »(univ, {a}), a) l :=
begin
  have [] [":", expr «expr = »(«expr \ »(univ, {a}), «expr ∪ »(Iio a, Ioi a))] [],
  { ext [] [] [],
    rw ["[", expr mem_diff_singleton, ",", expr «expr $ »(eq_true_intro, mem_univ x), ",", expr true_and, ",", expr ne_iff_lt_or_gt, "]"] [],
    refl },
  simp [] [] ["only"] ["[", expr this, ",", expr nhds_within_union, ",", expr tendsto_sup, ",", expr eventually_sup, "]"] [] ["at", "*"],
  exact [expr ⟨lhopital_zero_nhds_left hdf.1 hg'.1 hfa.1 hga.1 hdiv.1, lhopital_zero_nhds_right hdf.2 hg'.2 hfa.2 hga.2 hdiv.2⟩]
end

/-- **L'Hôpital's rule** for approaching a real, `deriv` version -/
theorem lhopital_zero_nhds (hdf : ∀ᶠx in 𝓝 a, DifferentiableAt ℝ f x) (hg' : ∀ᶠx in 𝓝 a, deriv g x ≠ 0)
  (hfa : tendsto f (𝓝 a) (𝓝 0)) (hga : tendsto g (𝓝 a) (𝓝 0))
  (hdiv : tendsto (fun x => (deriv f) x / (deriv g) x) (𝓝 a) l) : tendsto (fun x => f x / g x) (𝓝[univ \ {a}] a) l :=
  by 
    apply lhopital_zero_nhds' <;>
      first |
          apply eventually_nhds_within_of_eventually_nhds|
          apply tendsto_nhds_within_of_tendsto_nhds <;>
        assumption

-- error in Analysis.Calculus.Lhopital: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- **L'Hôpital's rule** for approaching +∞, `deriv` version -/
theorem lhopital_zero_at_top
(hdf : «expr∀ᶠ in , »((x : exprℝ()), at_top, differentiable_at exprℝ() f x))
(hg' : «expr∀ᶠ in , »((x : exprℝ()), at_top, «expr ≠ »(deriv g x, 0)))
(hftop : tendsto f at_top (expr𝓝() 0))
(hgtop : tendsto g at_top (expr𝓝() 0))
(hdiv : tendsto (λ x, «expr / »(deriv f x, deriv g x)) at_top l) : tendsto (λ x, «expr / »(f x, g x)) at_top l :=
begin
  have [ident hdg] [":", expr «expr∀ᶠ in , »((x), at_top, differentiable_at exprℝ() g x)] [],
  from [expr hg'.mp «expr $ »(eventually_of_forall, λ
    _ hg', classical.by_contradiction (λ h, hg' (deriv_zero_of_not_differentiable_at h)))],
  have [ident hdf'] [":", expr «expr∀ᶠ in , »((x), at_top, has_deriv_at f (deriv f x) x)] [],
  from [expr hdf.mp «expr $ »(eventually_of_forall, λ _, differentiable_at.has_deriv_at)],
  have [ident hdg'] [":", expr «expr∀ᶠ in , »((x), at_top, has_deriv_at g (deriv g x) x)] [],
  from [expr hdg.mp «expr $ »(eventually_of_forall, λ _, differentiable_at.has_deriv_at)],
  exact [expr has_deriv_at.lhopital_zero_at_top hdf' hdg' hg' hftop hgtop hdiv]
end

-- error in Analysis.Calculus.Lhopital: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- **L'Hôpital's rule** for approaching -∞, `deriv` version -/
theorem lhopital_zero_at_bot
(hdf : «expr∀ᶠ in , »((x : exprℝ()), at_bot, differentiable_at exprℝ() f x))
(hg' : «expr∀ᶠ in , »((x : exprℝ()), at_bot, «expr ≠ »(deriv g x, 0)))
(hfbot : tendsto f at_bot (expr𝓝() 0))
(hgbot : tendsto g at_bot (expr𝓝() 0))
(hdiv : tendsto (λ x, «expr / »(deriv f x, deriv g x)) at_bot l) : tendsto (λ x, «expr / »(f x, g x)) at_bot l :=
begin
  have [ident hdg] [":", expr «expr∀ᶠ in , »((x), at_bot, differentiable_at exprℝ() g x)] [],
  from [expr hg'.mp «expr $ »(eventually_of_forall, λ
    _ hg', classical.by_contradiction (λ h, hg' (deriv_zero_of_not_differentiable_at h)))],
  have [ident hdf'] [":", expr «expr∀ᶠ in , »((x), at_bot, has_deriv_at f (deriv f x) x)] [],
  from [expr hdf.mp «expr $ »(eventually_of_forall, λ _, differentiable_at.has_deriv_at)],
  have [ident hdg'] [":", expr «expr∀ᶠ in , »((x), at_bot, has_deriv_at g (deriv g x) x)] [],
  from [expr hdg.mp «expr $ »(eventually_of_forall, λ _, differentiable_at.has_deriv_at)],
  exact [expr has_deriv_at.lhopital_zero_at_bot hdf' hdg' hg' hfbot hgbot hdiv]
end

end deriv

