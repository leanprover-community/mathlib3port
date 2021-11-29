import Mathbin.Analysis.Calculus.MeanValue

/-!
# Extending differentiability to the boundary

We investigate how differentiable functions inside a set extend to differentiable functions
on the boundary. For this, it suffices that the function and its derivative admit limits there.
A general version of this statement is given in `has_fderiv_at_boundary_of_tendsto_fderiv`.

One-dimensional versions, in which one wants to obtain differentiability at the left endpoint or
the right endpoint of an interval, are given in
`has_deriv_at_interval_left_endpoint_of_tendsto_deriv` and
`has_deriv_at_interval_right_endpoint_of_tendsto_deriv`. These versions are formulated in terms
of the one-dimensional derivative `deriv ℝ f`.
-/


variable{E : Type _}[NormedGroup E][NormedSpace ℝ E]{F : Type _}[NormedGroup F][NormedSpace ℝ F]

open Filter Set Metric ContinuousLinearMap

open_locale TopologicalSpace

attribute [local mono] prod_mono

-- error in Analysis.Calculus.ExtendDeriv: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- If a function `f` is differentiable in a convex open set and continuous on its closure, and its
derivative converges to a limit `f'` at a point on the boundary, then `f` is differentiable there
with derivative `f'`. -/
theorem has_fderiv_at_boundary_of_tendsto_fderiv
{f : E → F}
{s : set E}
{x : E}
{f' : «expr →L[ ] »(E, exprℝ(), F)}
(f_diff : differentiable_on exprℝ() f s)
(s_conv : convex exprℝ() s)
(s_open : is_open s)
(f_cont : ∀ y «expr ∈ » closure s, continuous_within_at f s y)
(h : tendsto (λ y, fderiv exprℝ() f y) «expr𝓝[ ] »(s, x) (expr𝓝() f')) : has_fderiv_within_at f f' (closure s) x :=
begin
  classical,
  by_cases [expr hx, ":", expr «expr ∉ »(x, closure s)],
  { rw ["<-", expr closure_closure] ["at", ident hx],
    exact [expr has_fderiv_within_at_of_not_mem_closure hx] },
  push_neg ["at", ident hx],
  rw ["[", expr has_fderiv_within_at, ",", expr has_fderiv_at_filter, ",", expr asymptotics.is_o_iff, "]"] [],
  assume [binders (ε ε_pos)],
  obtain ["⟨", ident δ, ",", ident δ_pos, ",", ident hδ, "⟩", ":", expr «expr∃ , »((δ «expr > » 0), ∀
    y «expr ∈ » s, «expr < »(dist y x, δ) → «expr < »(«expr∥ ∥»(«expr - »(fderiv exprℝ() f y, f')), ε))],
  by simpa [] [] [] ["[", expr dist_zero_right, "]"] [] ["using", expr tendsto_nhds_within_nhds.1 h ε ε_pos],
  set [] [ident B] [] [":="] [expr ball x δ] [],
  suffices [] [":", expr ∀
   y «expr ∈ » «expr ∩ »(B, closure s), «expr ≤ »(«expr∥ ∥»(«expr - »(«expr - »(f y, f x), «expr - »(f' y, f' x))), «expr * »(ε, «expr∥ ∥»(«expr - »(y, x))))],
  from [expr mem_nhds_within_iff.2 ⟨δ, δ_pos, λ y hy, by simpa [] [] [] [] [] ["using", expr this y hy]⟩],
  suffices [] [":", expr ∀
   p : «expr × »(E, E), «expr ∈ »(p, closure («expr ∩ »(B, s).prod «expr ∩ »(B, s))) → «expr ≤ »(«expr∥ ∥»(«expr - »(«expr - »(f p.2, f p.1), «expr - »(f' p.2, f' p.1))), «expr * »(ε, «expr∥ ∥»(«expr - »(p.2, p.1))))],
  { rw [expr closure_prod_eq] ["at", ident this],
    intros [ident y, ident y_in],
    apply [expr this ⟨x, y⟩],
    have [] [":", expr «expr ⊆ »(«expr ∩ »(B, closure s), closure «expr ∩ »(B, s))] [],
    from [expr closure_inter_open is_open_ball],
    exact [expr ⟨this ⟨mem_ball_self δ_pos, hx⟩, this y_in⟩] },
  have [ident key] [":", expr ∀
   p : «expr × »(E, E), «expr ∈ »(p, «expr ∩ »(B, s).prod «expr ∩ »(B, s)) → «expr ≤ »(«expr∥ ∥»(«expr - »(«expr - »(f p.2, f p.1), «expr - »(f' p.2, f' p.1))), «expr * »(ε, «expr∥ ∥»(«expr - »(p.2, p.1))))] [],
  { rintros ["⟨", ident u, ",", ident v, "⟩", "⟨", ident u_in, ",", ident v_in, "⟩"],
    have [ident conv] [":", expr convex exprℝ() «expr ∩ »(B, s)] [":=", expr (convex_ball _ _).inter s_conv],
    have [ident diff] [":", expr differentiable_on exprℝ() f «expr ∩ »(B, s)] [":=", expr f_diff.mono (inter_subset_right _ _)],
    have [ident bound] [":", expr ∀
     z «expr ∈ » «expr ∩ »(B, s), «expr ≤ »(«expr∥ ∥»(«expr - »(fderiv_within exprℝ() f «expr ∩ »(B, s) z, f')), ε)] [],
    { intros [ident z, ident z_in],
      convert [] [expr le_of_lt (hδ _ z_in.2 z_in.1)] [],
      have [ident op] [":", expr is_open «expr ∩ »(B, s)] [":=", expr is_open_ball.inter s_open],
      rw [expr differentiable_at.fderiv_within _ (op.unique_diff_on z z_in)] [],
      exact [expr (diff z z_in).differentiable_at (is_open.mem_nhds op z_in)] },
    simpa [] [] [] [] [] ["using", expr conv.norm_image_sub_le_of_norm_fderiv_within_le' diff bound u_in v_in] },
  rintros ["⟨", ident u, ",", ident v, "⟩", ident uv_in],
  refine [expr continuous_within_at.closure_le uv_in _ _ key],
  have [ident f_cont'] [":", expr ∀ y «expr ∈ » closure s, continuous_within_at «expr - »(f, f') s y] [],
  { intros [ident y, ident y_in],
    exact [expr tendsto.sub (f_cont y y_in) f'.cont.continuous_within_at] },
  all_goals { have [] [":", expr «expr ⊆ »(«expr ∩ »(B, s).prod «expr ∩ »(B, s), s.prod s)] [],
    by mono [] [] [] []; exact [expr inter_subset_right _ _],
    obtain ["⟨", ident u_in, ",", ident v_in, "⟩", ":", expr «expr ∧ »(«expr ∈ »(u, closure s), «expr ∈ »(v, closure s))],
    by simpa [] [] [] ["[", expr closure_prod_eq, "]"] [] ["using", expr closure_mono this uv_in],
    apply [expr continuous_within_at.mono _ this],
    simp [] [] ["only"] ["[", expr continuous_within_at, "]"] [] [] },
  rw [expr nhds_within_prod_eq] [],
  { have [] [":", expr ∀
     u
     v, «expr = »(«expr - »(«expr - »(f v, f u), «expr - »(f' v, f' u)), «expr - »(«expr - »(f v, f' v), «expr - »(f u, f' u)))] [":=", expr by { intros [],
       abel [] [] [] }],
    simp [] [] ["only"] ["[", expr this, "]"] [] [],
    exact [expr tendsto.comp continuous_norm.continuous_at «expr $ »((tendsto.comp (f_cont' v v_in) tendsto_snd).sub, tendsto.comp (f_cont' u u_in) tendsto_fst)] },
  { apply [expr tendsto_nhds_within_of_tendsto_nhds],
    rw [expr nhds_prod_eq] [],
    exact [expr tendsto_const_nhds.mul «expr $ »(tendsto.comp continuous_norm.continuous_at, tendsto_snd.sub tendsto_fst)] }
end

-- error in Analysis.Calculus.ExtendDeriv: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- If a function is differentiable on the right of a point `a : ℝ`, continuous at `a`, and
its derivative also converges at `a`, then `f` is differentiable on the right at `a`. -/
theorem has_deriv_at_interval_left_endpoint_of_tendsto_deriv
{s : set exprℝ()}
{e : E}
{a : exprℝ()}
{f : exprℝ() → E}
(f_diff : differentiable_on exprℝ() f s)
(f_lim : continuous_within_at f s a)
(hs : «expr ∈ »(s, «expr𝓝[ ] »(Ioi a, a)))
(f_lim' : tendsto (λ x, deriv f x) «expr𝓝[ ] »(Ioi a, a) (expr𝓝() e)) : has_deriv_within_at f e (Ici a) a :=
begin
  obtain ["⟨", ident b, ",", ident ab, ",", ident sab, "⟩", ":", expr «expr∃ , »((b «expr ∈ » Ioi a), «expr ⊆ »(Ioc a b, s)), ":=", expr mem_nhds_within_Ioi_iff_exists_Ioc_subset.1 hs],
  let [ident t] [] [":=", expr Ioo a b],
  have [ident ts] [":", expr «expr ⊆ »(t, s)] [":=", expr subset.trans Ioo_subset_Ioc_self sab],
  have [ident t_diff] [":", expr differentiable_on exprℝ() f t] [":=", expr f_diff.mono ts],
  have [ident t_conv] [":", expr convex exprℝ() t] [":=", expr convex_Ioo a b],
  have [ident t_open] [":", expr is_open t] [":=", expr is_open_Ioo],
  have [ident t_closure] [":", expr «expr = »(closure t, Icc a b)] [":=", expr closure_Ioo ab],
  have [ident t_cont] [":", expr ∀ y «expr ∈ » closure t, continuous_within_at f t y] [],
  { rw [expr t_closure] [],
    assume [binders (y hy)],
    by_cases [expr h, ":", expr «expr = »(y, a)],
    { rw [expr h] [],
      exact [expr f_lim.mono ts] },
    { have [] [":", expr «expr ∈ »(y, s)] [":=", expr sab ⟨lt_of_le_of_ne hy.1 (ne.symm h), hy.2⟩],
      exact [expr (f_diff.continuous_on y this).mono ts] } },
  have [ident t_diff'] [":", expr tendsto (λ x, fderiv exprℝ() f x) «expr𝓝[ ] »(t, a) (expr𝓝() (smul_right 1 e))] [],
  { simp [] [] [] ["[", expr deriv_fderiv.symm, "]"] [] [],
    refine [expr tendsto.comp is_bounded_bilinear_map_smul_right.continuous_right.continuous_at _],
    exact [expr tendsto_nhds_within_mono_left Ioo_subset_Ioi_self f_lim'] },
  have [] [":", expr has_deriv_within_at f e (Icc a b) a] [],
  { rw ["[", expr has_deriv_within_at_iff_has_fderiv_within_at, ",", "<-", expr t_closure, "]"] [],
    exact [expr has_fderiv_at_boundary_of_tendsto_fderiv t_diff t_conv t_open t_cont t_diff'] },
  exact [expr this.nhds_within (mem_nhds_within_Ici_iff_exists_Icc_subset.2 ⟨b, ab, subset.refl _⟩)]
end

-- error in Analysis.Calculus.ExtendDeriv: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- If a function is differentiable on the left of a point `a : ℝ`, continuous at `a`, and
its derivative also converges at `a`, then `f` is differentiable on the left at `a`. -/
theorem has_deriv_at_interval_right_endpoint_of_tendsto_deriv
{s : set exprℝ()}
{e : E}
{a : exprℝ()}
{f : exprℝ() → E}
(f_diff : differentiable_on exprℝ() f s)
(f_lim : continuous_within_at f s a)
(hs : «expr ∈ »(s, «expr𝓝[ ] »(Iio a, a)))
(f_lim' : tendsto (λ x, deriv f x) «expr𝓝[ ] »(Iio a, a) (expr𝓝() e)) : has_deriv_within_at f e (Iic a) a :=
begin
  obtain ["⟨", ident b, ",", ident ba, ",", ident sab, "⟩", ":", expr «expr∃ , »((b «expr ∈ » Iio a), «expr ⊆ »(Ico b a, s)), ":=", expr mem_nhds_within_Iio_iff_exists_Ico_subset.1 hs],
  let [ident t] [] [":=", expr Ioo b a],
  have [ident ts] [":", expr «expr ⊆ »(t, s)] [":=", expr subset.trans Ioo_subset_Ico_self sab],
  have [ident t_diff] [":", expr differentiable_on exprℝ() f t] [":=", expr f_diff.mono ts],
  have [ident t_conv] [":", expr convex exprℝ() t] [":=", expr convex_Ioo b a],
  have [ident t_open] [":", expr is_open t] [":=", expr is_open_Ioo],
  have [ident t_closure] [":", expr «expr = »(closure t, Icc b a)] [":=", expr closure_Ioo ba],
  have [ident t_cont] [":", expr ∀ y «expr ∈ » closure t, continuous_within_at f t y] [],
  { rw [expr t_closure] [],
    assume [binders (y hy)],
    by_cases [expr h, ":", expr «expr = »(y, a)],
    { rw [expr h] [],
      exact [expr f_lim.mono ts] },
    { have [] [":", expr «expr ∈ »(y, s)] [":=", expr sab ⟨hy.1, lt_of_le_of_ne hy.2 h⟩],
      exact [expr (f_diff.continuous_on y this).mono ts] } },
  have [ident t_diff'] [":", expr tendsto (λ x, fderiv exprℝ() f x) «expr𝓝[ ] »(t, a) (expr𝓝() (smul_right 1 e))] [],
  { simp [] [] [] ["[", expr deriv_fderiv.symm, "]"] [] [],
    refine [expr tendsto.comp is_bounded_bilinear_map_smul_right.continuous_right.continuous_at _],
    exact [expr tendsto_nhds_within_mono_left Ioo_subset_Iio_self f_lim'] },
  have [] [":", expr has_deriv_within_at f e (Icc b a) a] [],
  { rw ["[", expr has_deriv_within_at_iff_has_fderiv_within_at, ",", "<-", expr t_closure, "]"] [],
    exact [expr has_fderiv_at_boundary_of_tendsto_fderiv t_diff t_conv t_open t_cont t_diff'] },
  exact [expr this.nhds_within (mem_nhds_within_Iic_iff_exists_Icc_subset.2 ⟨b, ba, subset.refl _⟩)]
end

-- error in Analysis.Calculus.ExtendDeriv: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- If a real function `f` has a derivative `g` everywhere but at a point, and `f` and `g` are
continuous at this point, then `g` is also the derivative of `f` at this point. -/
theorem has_deriv_at_of_has_deriv_at_of_ne
{f g : exprℝ() → E}
{x : exprℝ()}
(f_diff : ∀ y «expr ≠ » x, has_deriv_at f (g y) y)
(hf : continuous_at f x)
(hg : continuous_at g x) : has_deriv_at f (g x) x :=
begin
  have [ident A] [":", expr has_deriv_within_at f (g x) (Ici x) x] [],
  { have [ident diff] [":", expr differentiable_on exprℝ() f (Ioi x)] [":=", expr λ
     y hy, (f_diff y (ne_of_gt hy)).differentiable_at.differentiable_within_at],
    apply [expr has_deriv_at_interval_left_endpoint_of_tendsto_deriv diff hf.continuous_within_at self_mem_nhds_within],
    have [] [":", expr tendsto g «expr𝓝[ ] »(Ioi x, x) (expr𝓝() (g x))] [":=", expr tendsto_inf_left hg],
    apply [expr this.congr' _],
    apply [expr mem_of_superset self_mem_nhds_within (λ y hy, _)],
    exact [expr (f_diff y (ne_of_gt hy)).deriv.symm] },
  have [ident B] [":", expr has_deriv_within_at f (g x) (Iic x) x] [],
  { have [ident diff] [":", expr differentiable_on exprℝ() f (Iio x)] [":=", expr λ
     y hy, (f_diff y (ne_of_lt hy)).differentiable_at.differentiable_within_at],
    apply [expr has_deriv_at_interval_right_endpoint_of_tendsto_deriv diff hf.continuous_within_at self_mem_nhds_within],
    have [] [":", expr tendsto g «expr𝓝[ ] »(Iio x, x) (expr𝓝() (g x))] [":=", expr tendsto_inf_left hg],
    apply [expr this.congr' _],
    apply [expr mem_of_superset self_mem_nhds_within (λ y hy, _)],
    exact [expr (f_diff y (ne_of_lt hy)).deriv.symm] },
  simpa [] [] [] [] [] ["using", expr B.union A]
end

/-- If a real function `f` has a derivative `g` everywhere but at a point, and `f` and `g` are
continuous at this point, then `g` is the derivative of `f` everywhere. -/
theorem has_deriv_at_of_has_deriv_at_of_ne' {f g : ℝ → E} {x : ℝ} (f_diff : ∀ y (_ : y ≠ x), HasDerivAt f (g y) y)
  (hf : ContinuousAt f x) (hg : ContinuousAt g x) (y : ℝ) : HasDerivAt f (g y) y :=
  by 
    rcases eq_or_ne y x with (rfl | hne)
    ·
      exact has_deriv_at_of_has_deriv_at_of_ne f_diff hf hg
    ·
      exact f_diff y hne

