import Mathbin.MeasureTheory.Integral.SetIntegral 
import Mathbin.Analysis.Calculus.MeanValue

/-!
# Derivatives of integrals depending on parameters

A parametric integral is a function with shape `f = λ x : H, ∫ a : α, F x a ∂μ` for some
`F : H → α → E`, where `H` and `E` are normed spaces and `α` is a measured space with measure `μ`.

We already know from `continuous_of_dominated` in `measure_theory.integral.bochner` how to
guarantee that `f` is continuous using the dominated convergence theorem. In this file,
we want to express the derivative of `f` as the integral of the derivative of `F` with respect
to `x`.


## Main results

As explained above, all results express the derivative of a parametric integral as the integral of
a derivative. The variations come from the assumptions and from the different ways of expressing
derivative, especially Fréchet derivatives vs elementary derivative of function of one real
variable.

* `has_fderiv_at_of_dominated_loc_of_lip`: this version assumes
    `F x` is ae-measurable for x near `x₀`, `F x₀` is integrable,
    `λ x, F x a` has derivative `F' a : H →L[ℝ] E` at `x₀` which is ae-measurable,
    `λ x, F x a` is locally Lipschitz near `x₀` for almost every `a`, with a Lipschitz bound which
    is integrable with respect to `a`. A subtle point is that the "near x₀" in the last condition
    has to be uniform in `a`. This is controlled by a positive number `ε`.

* `has_fderiv_at_of_dominated_of_fderiv_le`: this version assume `λ x, F x a` has derivative
    `F' x a` for `x` near `x₀` and `F' x` is bounded by an integrable function independent from
    `x` near `x₀`.


`has_deriv_at_of_dominated_loc_of_lip` and `has_deriv_at_of_dominated_loc_of_deriv_le ` are versions
of the above two results that assume `H = ℝ` and use the high-school derivative `deriv` instead of
Fréchet derivative `fderiv`.
-/


noncomputable theory

open TopologicalSpace MeasureTheory Filter Metric

open_locale TopologicalSpace Filter

variable{α :
    Type
      _}[MeasurableSpace
      α]{μ :
    Measureₓ
      α}{E :
    Type
      _}[NormedGroup
      E][NormedSpace ℝ
      E][CompleteSpace
      E][second_countable_topology
      E][MeasurableSpace
      E][BorelSpace E]{H : Type _}[NormedGroup H][NormedSpace ℝ H][second_countable_topology$ H →L[ℝ] E]

-- error in Analysis.Calculus.ParametricIntegral: ././Mathport/Syntax/Translate/Basic.lean:340:40: in exacts: ././Mathport/Syntax/Translate/Tactic/Basic.lean:41:45: missing argument
/-- Differentiation under integral of `x ↦ ∫ F x a` at a given point `x₀`, assuming
`F x₀` is integrable, `x ↦ F x a` is locally Lipschitz on a ball around `x₀` for ae `a` with
integrable Lipschitz bound (with a ball radius independent of `a`), and `F x` is
ae-measurable for `x` in the same ball. See `has_fderiv_at_of_dominated_loc_of_lip` for a
slightly more general version. -/
theorem has_fderiv_at_of_dominated_loc_of_lip'
{F : H → α → E}
{F' : α → «expr →L[ ] »(H, exprℝ(), E)}
{x₀ : H}
{bound : α → exprℝ()}
{ε : exprℝ()}
(ε_pos : «expr < »(0, ε))
(hF_meas : ∀ x «expr ∈ » ball x₀ ε, ae_measurable (F x) μ)
(hF_int : integrable (F x₀) μ)
(hF'_meas : ae_measurable F' μ)
(h_lipsch : «expr∀ᵐ ∂ , »((a), μ, lipschitz_on_with «expr $ »(real.nnabs, bound a) (λ x, F x a) (ball x₀ ε)))
(bound_integrable : integrable (bound : α → exprℝ()) μ)
(h_diff : «expr∀ᵐ ∂ , »((a), μ, has_fderiv_at (λ
   x, F x a) (F' a) x₀)) : «expr ∧ »(integrable F' μ, has_fderiv_at (λ
  x, «expr∫ , ∂ »((a), F x a, μ)) «expr∫ , ∂ »((a), F' a, μ) x₀) :=
begin
  have [ident x₀_in] [":", expr «expr ∈ »(x₀, ball x₀ ε)] [":=", expr mem_ball_self ε_pos],
  have [ident nneg] [":", expr ∀
   x, «expr ≤ »(0, «expr ⁻¹»(«expr∥ ∥»(«expr - »(x, x₀))))] [":=", expr λ x, inv_nonneg.mpr (norm_nonneg _)],
  set [] [ident b] [":", expr α → exprℝ()] [":="] [expr λ a, «expr| |»(bound a)] [],
  have [ident b_int] [":", expr integrable b μ] [":=", expr bound_integrable.norm],
  have [ident b_nonneg] [":", expr ∀ a, «expr ≤ »(0, b a)] [":=", expr λ a, abs_nonneg _],
  have [ident hF_int'] [":", expr ∀ x «expr ∈ » ball x₀ ε, integrable (F x) μ] [],
  { intros [ident x, ident x_in],
    have [] [":", expr «expr∀ᵐ ∂ , »((a), μ, «expr ≤ »(«expr∥ ∥»(«expr - »(F x₀ a, F x a)), «expr * »(ε, «expr∥ ∥»((bound a : exprℝ())))))] [],
    { apply [expr h_lipsch.mono],
      intros [ident a, ident ha],
      rw [expr lipschitz_on_with_iff_norm_sub_le] ["at", ident ha],
      apply [expr (ha x₀ x₀_in x x_in).trans],
      rw ["[", expr mul_comm, ",", expr real.coe_nnabs, ",", expr real.norm_eq_abs, "]"] [],
      rw ["[", expr mem_ball, ",", expr dist_eq_norm, ",", expr norm_sub_rev, "]"] ["at", ident x_in],
      exact [expr mul_le_mul_of_nonneg_right (le_of_lt x_in) (abs_nonneg _)] },
    exact [expr integrable_of_norm_sub_le (hF_meas x x_in) hF_int (integrable.const_mul bound_integrable.norm ε) this] },
  have [ident hF'_int] [":", expr integrable F' μ] [],
  { have [] [":", expr «expr∀ᵐ ∂ , »((a), μ, «expr ≤ »(«expr∥ ∥»(F' a), b a))] [],
    { apply [expr (h_diff.and h_lipsch).mono],
      rintros [ident a, "⟨", ident ha_diff, ",", ident ha_lip, "⟩"],
      exact [expr ha_diff.le_of_lip (ball_mem_nhds _ ε_pos) ha_lip] },
    exact [expr b_int.mono' hF'_meas this] },
  refine [expr ⟨hF'_int, _⟩],
  have [ident h_ball] [":", expr «expr ∈ »(ball x₀ ε, expr𝓝() x₀)] [":=", expr ball_mem_nhds x₀ ε_pos],
  have [] [":", expr «expr∀ᶠ in , »((x), expr𝓝() x₀, «expr = »(«expr * »(«expr ⁻¹»(«expr∥ ∥»(«expr - »(x, x₀))), «expr∥ ∥»(«expr - »(«expr - »(«expr∫ , ∂ »((a), F x a, μ), «expr∫ , ∂ »((a), F x₀ a, μ)), «expr∫ , ∂ »((a), F' a, μ) «expr - »(x, x₀)))), «expr∥ ∥»(«expr∫ , ∂ »((a), «expr • »(«expr ⁻¹»(«expr∥ ∥»(«expr - »(x, x₀))), «expr - »(«expr - »(F x a, F x₀ a), F' a «expr - »(x, x₀))), μ))))] [],
  { apply [expr mem_of_superset (ball_mem_nhds _ ε_pos)],
    intros [ident x, ident x_in],
    rw ["[", expr set.mem_set_of_eq, ",", "<-", expr norm_smul_of_nonneg (nneg _), ",", expr integral_smul, ",", expr integral_sub, ",", expr integral_sub, ",", "<-", expr continuous_linear_map.integral_apply hF'_int, "]"] [],
    exacts ["[", expr hF_int' x x_in, ",", expr hF_int, ",", expr (hF_int' x x_in).sub hF_int, ",", expr hF'_int.apply_continuous_linear_map _, "]"] },
  rw ["[", expr has_fderiv_at_iff_tendsto, ",", expr tendsto_congr' this, ",", "<-", expr tendsto_zero_iff_norm_tendsto_zero, ",", "<-", expr show «expr = »(«expr∫ , ∂ »((a : α), «expr • »(«expr ⁻¹»(«expr∥ ∥»(«expr - »(x₀, x₀))), «expr - »(«expr - »(F x₀ a, F x₀ a), F' a «expr - »(x₀, x₀))), μ), 0), by simp [] [] [] [] [] [], "]"] [],
  apply [expr tendsto_integral_filter_of_dominated_convergence],
  { filter_upwards ["[", expr h_ball, "]"] [],
    intros [ident x, ident x_in],
    apply [expr ae_measurable.const_smul],
    exact [expr ((hF_meas _ x_in).sub (hF_meas _ x₀_in)).sub (hF'_meas.apply_continuous_linear_map _)] },
  { apply [expr mem_of_superset h_ball],
    intros [ident x, ident hx],
    apply [expr (h_diff.and h_lipsch).mono],
    rintros [ident a, "⟨", ident ha_deriv, ",", ident ha_bound, "⟩"],
    show [expr «expr ≤ »(«expr∥ ∥»(«expr • »(«expr ⁻¹»(«expr∥ ∥»(«expr - »(x, x₀))), «expr - »(«expr - »(F x a, F x₀ a), F' a «expr - »(x, x₀)))), «expr + »(b a, «expr∥ ∥»(F' a)))],
    replace [ident ha_bound] [":", expr «expr ≤ »(«expr∥ ∥»(«expr - »(F x a, F x₀ a)), «expr * »(b a, «expr∥ ∥»(«expr - »(x, x₀))))] [],
    { rw [expr lipschitz_on_with_iff_norm_sub_le] ["at", ident ha_bound],
      exact [expr ha_bound _ hx _ x₀_in] },
    calc
      «expr = »(«expr∥ ∥»(«expr • »(«expr ⁻¹»(«expr∥ ∥»(«expr - »(x, x₀))), «expr - »(«expr - »(F x a, F x₀ a), F' a «expr - »(x, x₀)))), «expr∥ ∥»(«expr - »(«expr • »(«expr ⁻¹»(«expr∥ ∥»(«expr - »(x, x₀))), «expr - »(F x a, F x₀ a)), «expr • »(«expr ⁻¹»(«expr∥ ∥»(«expr - »(x, x₀))), F' a «expr - »(x, x₀))))) : by rw [expr smul_sub] []
      «expr ≤ »(..., «expr + »(«expr∥ ∥»(«expr • »(«expr ⁻¹»(«expr∥ ∥»(«expr - »(x, x₀))), «expr - »(F x a, F x₀ a))), «expr∥ ∥»(«expr • »(«expr ⁻¹»(«expr∥ ∥»(«expr - »(x, x₀))), F' a «expr - »(x, x₀))))) : norm_sub_le _ _
      «expr = »(..., «expr + »(«expr * »(«expr ⁻¹»(«expr∥ ∥»(«expr - »(x, x₀))), «expr∥ ∥»(«expr - »(F x a, F x₀ a))), «expr * »(«expr ⁻¹»(«expr∥ ∥»(«expr - »(x, x₀))), «expr∥ ∥»(F' a «expr - »(x, x₀))))) : by { rw ["[", expr norm_smul_of_nonneg, ",", expr norm_smul_of_nonneg, "]"] []; exact [expr nneg _] }
      «expr ≤ »(..., «expr + »(«expr * »(«expr ⁻¹»(«expr∥ ∥»(«expr - »(x, x₀))), «expr * »(b a, «expr∥ ∥»(«expr - »(x, x₀)))), «expr * »(«expr ⁻¹»(«expr∥ ∥»(«expr - »(x, x₀))), «expr * »(«expr∥ ∥»(F' a), «expr∥ ∥»(«expr - »(x, x₀)))))) : add_le_add _ _
      «expr ≤ »(..., «expr + »(b a, «expr∥ ∥»(F' a))) : _,
    exact [expr mul_le_mul_of_nonneg_left ha_bound (nneg _)],
    apply [expr mul_le_mul_of_nonneg_left ((F' a).le_op_norm _) (nneg _)],
    by_cases [expr h, ":", expr «expr = »(«expr∥ ∥»(«expr - »(x, x₀)), 0)],
    { simpa [] [] [] ["[", expr h, "]"] [] ["using", expr add_nonneg (b_nonneg a) (norm_nonneg (F' a))] },
    { field_simp [] ["[", expr h, "]"] [] [] } },
  { exact [expr b_int.add hF'_int.norm] },
  { apply [expr h_diff.mono],
    intros [ident a, ident ha],
    suffices [] [":", expr tendsto (λ
      x, «expr • »(«expr ⁻¹»(«expr∥ ∥»(«expr - »(x, x₀))), «expr - »(«expr - »(F x a, F x₀ a), F' a «expr - »(x, x₀)))) (expr𝓝() x₀) (expr𝓝() 0)],
    by simpa [] [] [] [] [] [],
    rw [expr tendsto_zero_iff_norm_tendsto_zero] [],
    have [] [":", expr «expr = »(λ
      x, «expr * »(«expr ⁻¹»(«expr∥ ∥»(«expr - »(x, x₀))), «expr∥ ∥»(«expr - »(«expr - »(F x a, F x₀ a), F' a «expr - »(x, x₀)))), λ
      x, «expr∥ ∥»(«expr • »(«expr ⁻¹»(«expr∥ ∥»(«expr - »(x, x₀))), «expr - »(«expr - »(F x a, F x₀ a), F' a «expr - »(x, x₀)))))] [],
    { ext [] [ident x] [],
      rw [expr norm_smul_of_nonneg (nneg _)] [] },
    rwa ["[", expr has_fderiv_at_iff_tendsto, ",", expr this, "]"] ["at", ident ha] }
end

/-- Differentiation under integral of `x ↦ ∫ F x a` at a given point `x₀`, assuming
`F x₀` is integrable, `x ↦ F x a` is locally Lipschitz on a ball around `x₀` for ae `a`
(with a ball radius independent of `a`) with integrable Lipschitz bound, and `F x` is ae-measurable
for `x` in a possibly smaller neighborhood of `x₀`. -/
theorem has_fderiv_at_of_dominated_loc_of_lip {F : H → α → E} {F' : α → H →L[ℝ] E} {x₀ : H} {bound : α → ℝ} {ε : ℝ}
  (ε_pos : 0 < ε) (hF_meas : ∀ᶠx in 𝓝 x₀, AeMeasurable (F x) μ) (hF_int : integrable (F x₀) μ)
  (hF'_meas : AeMeasurable F' μ) (h_lip : ∀ᵐa ∂μ, LipschitzOnWith (Real.nnabs$ bound a) (fun x => F x a) (ball x₀ ε))
  (bound_integrable : integrable (bound : α → ℝ) μ) (h_diff : ∀ᵐa ∂μ, HasFderivAt (fun x => F x a) (F' a) x₀) :
  integrable F' μ ∧ HasFderivAt (fun x => ∫a, F x a ∂μ) (∫a, F' a ∂μ) x₀ :=
  by 
    obtain ⟨ε', ε'_pos, h'⟩ : ∃ (ε' : _)(_ : ε' > 0), ∀ x _ : x ∈ ball x₀ ε', AeMeasurable (F x) μ
    ·
      simpa using nhds_basis_ball.eventually_iff.mp hF_meas 
    set δ := min ε ε' 
    have δ_pos : 0 < δ := lt_minₓ ε_pos ε'_pos 
    replace h' : ∀ x, x ∈ ball x₀ δ → AeMeasurable (F x) μ
    ·
      intro x x_in 
      exact h' _ (ball_subset_ball (min_le_rightₓ ε ε') x_in)
    replace h_lip : ∀ᵐa : α ∂μ, LipschitzOnWith (Real.nnabs$ bound a) (fun x => F x a) (ball x₀ δ)
    ·
      apply h_lip.mono 
      intro a lip 
      exact lip.mono (ball_subset_ball$ min_le_leftₓ ε ε')
    apply has_fderiv_at_of_dominated_loc_of_lip' δ_pos <;> assumption

/-- Differentiation under integral of `x ↦ ∫ F x a` at a given point `x₀`, assuming
`F x₀` is integrable, `x ↦ F x a` is differentiable on a ball around `x₀` for ae `a` with
derivative norm uniformly bounded by an integrable function (the ball radius is independent of `a`),
and `F x` is ae-measurable for `x` in a possibly smaller neighborhood of `x₀`. -/
theorem has_fderiv_at_of_dominated_of_fderiv_le {F : H → α → E} {F' : H → α → H →L[ℝ] E} {x₀ : H} {bound : α → ℝ}
  {ε : ℝ} (ε_pos : 0 < ε) (hF_meas : ∀ᶠx in 𝓝 x₀, AeMeasurable (F x) μ) (hF_int : integrable (F x₀) μ)
  (hF'_meas : AeMeasurable (F' x₀) μ) (h_bound : ∀ᵐa ∂μ, ∀ x _ : x ∈ ball x₀ ε, ∥F' x a∥ ≤ bound a)
  (bound_integrable : integrable (bound : α → ℝ) μ)
  (h_diff : ∀ᵐa ∂μ, ∀ x _ : x ∈ ball x₀ ε, HasFderivAt (fun x => F x a) (F' x a) x) :
  HasFderivAt (fun x => ∫a, F x a ∂μ) (∫a, F' x₀ a ∂μ) x₀ :=
  by 
    have x₀_in : x₀ ∈ ball x₀ ε := mem_ball_self ε_pos 
    have diff_x₀ : ∀ᵐa ∂μ, HasFderivAt (fun x => F x a) (F' x₀ a) x₀ := h_diff.mono fun a ha => ha x₀ x₀_in 
    have  : ∀ᵐa ∂μ, LipschitzOnWith (Real.nnabs (bound a)) (fun x => F x a) (ball x₀ ε)
    ·
      apply (h_diff.and h_bound).mono 
      rintro a ⟨ha_deriv, ha_bound⟩
      refine'
        (convex_ball _ _).lipschitz_on_with_of_nnnorm_has_fderiv_within_le
          (fun x x_in => (ha_deriv x x_in).HasFderivWithinAt) fun x x_in => _ 
      rw [←Nnreal.coe_le_coe, coe_nnnorm, Real.coe_nnabs]
      exact (ha_bound x x_in).trans (le_abs_self _)
    exact (has_fderiv_at_of_dominated_loc_of_lip ε_pos hF_meas hF_int hF'_meas this bound_integrable diff_x₀).2

/-- Derivative under integral of `x ↦ ∫ F x a` at a given point `x₀ : ℝ`, assuming
`F x₀` is integrable, `x ↦ F x a` is locally Lipschitz on an interval around `x₀` for ae `a`
(with interval radius independent of `a`) with integrable Lipschitz bound, and `F x` is
ae-measurable for `x` in a possibly smaller neighborhood of `x₀`. -/
theorem has_deriv_at_of_dominated_loc_of_lip {F : ℝ → α → E} {F' : α → E} {x₀ : ℝ} {ε : ℝ} (ε_pos : 0 < ε)
  (hF_meas : ∀ᶠx in 𝓝 x₀, AeMeasurable (F x) μ) (hF_int : integrable (F x₀) μ) (hF'_meas : AeMeasurable F' μ)
  {bound : α → ℝ} (h_lipsch : ∀ᵐa ∂μ, LipschitzOnWith (Real.nnabs$ bound a) (fun x => F x a) (ball x₀ ε))
  (bound_integrable : integrable (bound : α → ℝ) μ) (h_diff : ∀ᵐa ∂μ, HasDerivAt (fun x => F x a) (F' a) x₀) :
  integrable F' μ ∧ HasDerivAt (fun x => ∫a, F x a ∂μ) (∫a, F' a ∂μ) x₀ :=
  by 
    have hm := (ContinuousLinearMap.smulRightL ℝ ℝ E 1).Continuous.Measurable.comp_ae_measurable hF'_meas 
    cases' has_fderiv_at_of_dominated_loc_of_lip ε_pos hF_meas hF_int hm h_lipsch bound_integrable h_diff with hF'_int
      key 
    replace hF'_int : integrable F' μ
    ·
      rw [←integrable_norm_iff hm] at hF'_int 
      simpa only [integrable_norm_iff, hF'_meas, one_mulₓ, norm_one, ContinuousLinearMap.norm_smul_rightL_apply] using
        hF'_int 
    refine' ⟨hF'_int, _⟩
    simpRw [has_deriv_at_iff_has_fderiv_at]  at h_diff⊢
    rwa [ContinuousLinearMap.integral_comp_comm _ hF'_int] at key 
    all_goals 
      infer_instance

/-- Derivative under integral of `x ↦ ∫ F x a` at a given point `x₀ : ℝ`, assuming
`F x₀` is integrable, `x ↦ F x a` is differentiable on an interval around `x₀` for ae `a`
(with interval radius independent of `a`) with derivative uniformly bounded by an integrable
function, and `F x` is ae-measurable for `x` in a possibly smaller neighborhood of `x₀`. -/
theorem has_deriv_at_of_dominated_loc_of_deriv_le {F : ℝ → α → E} {F' : ℝ → α → E} {x₀ : ℝ} {ε : ℝ} (ε_pos : 0 < ε)
  (hF_meas : ∀ᶠx in 𝓝 x₀, AeMeasurable (F x) μ) (hF_int : integrable (F x₀) μ) (hF'_meas : AeMeasurable (F' x₀) μ)
  {bound : α → ℝ} (h_bound : ∀ᵐa ∂μ, ∀ x _ : x ∈ ball x₀ ε, ∥F' x a∥ ≤ bound a) (bound_integrable : integrable bound μ)
  (h_diff : ∀ᵐa ∂μ, ∀ x _ : x ∈ ball x₀ ε, HasDerivAt (fun x => F x a) (F' x a) x) :
  integrable (F' x₀) μ ∧ HasDerivAt (fun n => ∫a, F n a ∂μ) (∫a, F' x₀ a ∂μ) x₀ :=
  by 
    have x₀_in : x₀ ∈ ball x₀ ε := mem_ball_self ε_pos 
    have diff_x₀ : ∀ᵐa ∂μ, HasDerivAt (fun x => F x a) (F' x₀ a) x₀ := h_diff.mono fun a ha => ha x₀ x₀_in 
    have  : ∀ᵐa ∂μ, LipschitzOnWith (Real.nnabs (bound a)) (fun x : ℝ => F x a) (ball x₀ ε)
    ·
      apply (h_diff.and h_bound).mono 
      rintro a ⟨ha_deriv, ha_bound⟩
      refine'
        (convex_ball _ _).lipschitz_on_with_of_nnnorm_has_deriv_within_le
          (fun x x_in => (ha_deriv x x_in).HasDerivWithinAt) fun x x_in => _ 
      rw [←Nnreal.coe_le_coe, coe_nnnorm, Real.coe_nnabs]
      exact (ha_bound x x_in).trans (le_abs_self _)
    exact has_deriv_at_of_dominated_loc_of_lip ε_pos hF_meas hF_int hF'_meas this bound_integrable diff_x₀

